# Second review, spot 8: `Def_BitcoinTaproot` against the version-1 branch and Tapscript

Independent second review (the first reviewer's reports were not read). Core revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`.

Core:
- `VerifyWitnessProgram`, version-1 branch (annex, key path, control block, leaf version, weight budget): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1955-L1999
- `ExecuteWitnessScript` (OP_SUCCESSx scan, initial stack limit, element size, clean stack): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1842-L1880
- `EvalScript` Tapscript rules (no `MAX_SCRIPT_SIZE`, no op count, `MINIMALIF`, `OP_CHECKSIGADD`, `OP_CHECKMULTISIG`, `OP_CODESEPARATOR` position): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L417-L1249
- `EvalChecksigTapscript`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L357-L394
- `SignatureHashSchnorr`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1493-L1573
- `CheckSchnorrSignature`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1727-L1753
- `ComputeTapleafHash`, `ComputeTapbranchHash`, `ComputeTaprootMerkleRoot`, `VerifyTaprootCommitment`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1882-L1925
- `XOnlyPubKey::CheckTapTweak`, `ComputeTapTweakHash`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp#L246-L263
- `IsOpSuccess`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.cpp#L365-L370
- constants: `ANNEX_TAG`, `VALIDATION_WEIGHT_*` (`script.h` L59–L65), `TAPROOT_*`, `WITNESS_V1_TAPROOT_SIZE` (`interpreter.h` L238–L247)

Lean: `/home/user/prove2me/Definitions/Def_BitcoinTaproot.lean` (`tapleafHash`, `tapbranchHash`,
`taprootMerkleRoot`, `checkTapTweak`, `verifyTaprootCommitment`, `sigHashSchnorr`,
`checkSchnorrSignature`, `isOpSuccess`, `opSuccessScan`, `evalChecksigTapscript`, `tapExecOp`, `tapStep`,
`tapRun`, `executeTapscript`, `witnessSerializedSize`, `hasAnnex`, `taprootHandler`). Blind read-back
used: `scratchpad/audit13/readback_Def_BitcoinTaproot.md` (present).

## Verdict

**No defect found.** The handler reproduces the version-1 branch: empty witness fails; the annex is
detected on the raw witness (≥ 2 elements, last non-empty, first byte `0x50`) and hashed as the
serialized vector; one element after the annex is the key path (`CheckSchnorrSignature` with
`TAPROOT`, 64/65 bytes, explicit `0x00` hash type invalid, `SIGHASH_SINGLE` without a matching output
invalid, hash types outside `{0..3, 0x81..0x83}` invalid); otherwise control and script are popped,
the control size must be `33 + 32k` with `k ≤ 128`, the leaf hash uses `control[0] & 0xfe`, the
commitment is `CheckTapTweak(program, control[1..33], root, control[0] & 1)` with a BIP340 `lift_x`
of the internal key, `t < n` and the tweaked point's abscissa and parity; leaf version `0xc0` runs
Tapscript with the budget `GetSerializeSize(witness.stack) + 50` over the *whole* witness (annex
included), and any other leaf version succeeds (`DISCOURAGE_UPGRADABLE_TAPROOT_VERSION` is policy).
Tapscript execution: the `OP_SUCCESSx` scan precedes everything (a malformed push before the first
success opcode fails, after it succeeds; the scan overrides stack-size and element-size limits);
then the 1000-element initial limit, the 520-byte elements, no `MAX_SCRIPT_SIZE`, no operation count,
`MINIMALIF` as consensus for `OP_IF`/`OP_NOTIF` when executed, `OP_CHECKSIG(VERIFY)` and
`OP_CHECKSIGADD` (`sig num pubkey`, 4-byte `num`, 5-byte result allowed) through
`EvalChecksigTapscript` (50 weight per non-empty signature including with unknown key types, empty
pubkey fails, 32-byte keys checked only for non-empty signatures, other sizes succeed since
`DISCOURAGE_UPGRADABLE_PUBKEYTYPE` is policy), `OP_CHECKMULTISIG(VERIFY)` failing only when executed,
`OP_CODESEPARATOR` recording the opcode position (counting every instruction, pushes and skipped ones
included, only when executed), the stack-size limit after every instruction, the unbalanced-conditional
test and the exactly-one-true-element rule. `SignatureHashSchnorr` matches field by field, including
`ext_flag` (`spend_type = 2·ext_flag + annex`), `key_version = 0` and the code-separator position.
The only observation (not a defect): the disabled-opcode test in `tapStep` is unreachable, as the
Lean comment says, because every disabled opcode is an `OP_SUCCESSx`.

## `VerifyWitnessProgram` (version 1) ↔ `taprootHandler`

| Core | Lean |
|---|---|
| gated by `witversion == 1 && program.size() == 32 && !is_p2sh` and `SCRIPT_VERIFY_TAPROOT` | gated in `BitcoinVerify.verifyWitnessProgram` (spot 7) |
| `stack.size() == 0 → WITNESS_EMPTY` | `witness.isEmpty → false` |
| `size ≥ 2 && !back.empty() && back[0] == 0x50`: pop; `annex_hash = SHA256(CompactSize‖annex)` | `hasAnnex`; `annex? := getLast?`; `stack := dropLast`; `sha256 (serBytes a)` |
| `size == 1`: `CheckSchnorrSignature(front, program, TAPROOT)` | `checkSchnorrSignature tx spent nIn (stack.getD 0 []) program false ed0` |
| `control = pop; script = pop`; `size < 33 ∨ > 4129 ∨ (size − 33) % 32 ≠ 0 → WRONG_CONTROL_SIZE` | same three tests (the `Nat` subtraction is guarded by the first disjunct) |
| `tapleaf = ComputeTapleafHash(control[0] & 0xfe, script)`; `!VerifyTaprootCommitment → MISMATCH` | `tapleafHash (ofNat 8 (c0 &&& 0xfe)) script`; `verifyTaprootCommitment control program leafHash` |
| leaf `0xc0`: `weight = GetSerializeSize(witness.stack) + 50`; `ExecuteWitnessScript(TAPSCRIPT)` | `executeTapscript tc {ed0 with tapleafHash} stack.reverse script (witnessSerializedSize witness + 50)` |
| other leaf versions: policy flag, else success | `true` |

`witnessSerializedSize` is `serList serBytes witness` (count + each element with its CompactSize) =
`GetSerializeSize(std::vector<std::vector<unsigned char>>)`; the vector passed is the original
`witness.stack`, annex and control included, in both.

## `ComputeTapleafHash` / `ComputeTapbranchHash` / `ComputeTaprootMerkleRoot` / `VerifyTaprootCommitment` / `CheckTapTweak`

`TapLeaf(version ‖ CompactSize(len) ‖ script)`; `TapBranch` of the lexicographically smaller first
(`lexLt` is `std::lexicographical_compare` on bytes); the fold over the 32-byte nodes after the 33-byte
base; `p = control[1..33]`, `q = program`, parity `control[0] & 1`. `checkTapTweak`: `liftX internal`
(`secp256k1_xonly_pubkey_parse`: `x < p` and on the curve, even `y`), `t = TapTweak(internal ‖ root)`,
`t < n` (`secp256k1_ec_pubkey_tweak_add` overflow), `Q = P + tG ≠ ∞`, `x(Q) = program` and
`odd(y(Q)) = parity`. Match.

## `SignatureHashSchnorr` ↔ `sigHashSchnorr`

Epoch `0`; `hash_type` byte (validity `≤ 3 ∨ 0x81..0x83`); `version` (uint32), `nLockTime`; if not
ANYONECANPAY the four single-SHA256s (prevouts, spent amounts as int64, spent scripts with
CompactSize, sequences); if `output_type = ALL` the outputs hash (`output_type` is `ALL` for
`SIGHASH_DEFAULT`, else `hash_type & 3`); `spend_type`; ANYONECANPAY → prevout, spent `CTxOut`,
sequence, else `in_pos` (uint32); annex hash; `SINGLE` → `in_pos < vout.size()` else `false`, the
output's SHA256; `TAPSCRIPT` → tapleaf hash, `key_version = 0`, `codeseparator_pos` (uint32). Lean
computes the same byte string under `tagged "TapSighash"`. Match (including the key-path vs
script-path `ext_flag` and `key_version` bytes; vectors with input 1 and the code-separator position
7 confirm the serialization).

## `CheckSchnorrSignature` ↔ `checkSchnorrSignature`

64 or 65 bytes; a 65th byte equal to `0x00` → `SCHNORR_SIG_HASHTYPE`; `SignatureHashSchnorr` false →
`SCHNORR_SIG_HASHTYPE`; BIP340 verification. Lean identical; `BitcoinSig.schnorrVerify` is the BIP340
equation (`r < p`, `s < n`, `lift_x(pk)`, `R = sG − eP`, even `y`, `x = r`).

## `ExecuteWitnessScript` (Tapscript) ↔ `executeTapscript`

Scan with `GetOp` (`BAD_OPCODE` on a malformed push before any success opcode; success on the first
`IsOpSuccess`, policy flag aside) → `stack.size() > 1000 → STACK_SIZE` → elements `> 520 → PUSH_SIZE`
→ `EvalScript` → `size ≠ 1 → CLEANSTACK` → `!CastToBool → EVAL_FALSE`. Lean: `opSuccessScan`
(`none`/`some true`/`some false`), `1000 < stack.length`, `stack.any (520 <)`, `parseScript` (cannot
fail after a full scan), `tapRun`, `length = 1 && topTrue`. `isOpSuccess` is the exact set
`{80, 98, 126–129, 131–134, 137–138, 141–142, 149–153, 187–254}`. Match.

## `EvalScript` under `TAPSCRIPT` ↔ `tapStep` / `tapExecOp` / `evalChecksigTapscript`

- No `MAX_SCRIPT_SIZE`, no `nOpCount` (`sigversion` tests in Core); `tapStep` has neither.
- Push size and the stack limit after every instruction: as in BASE.
- `OP_IF`/`OP_NOTIF` executed: `vch.size() > 1 ∨ (size == 1 ∧ vch[0] ≠ 1) → TAPSCRIPT_MINIMALIF`
  before `CastToBool`; `tapExecOp` tests `1 < top.length ∨ (top.length = 1 ∧ top[0] ≠ 1)` then defers to
  `execOp` (which pops and pushes the condition). Skipped `IF`/`NOTIF` push `false` without a stack test.
- `OP_CHECKSIG(VERIFY)`: `sig = stacktop(-2)`, `pubkey = top`; `EvalChecksigTapscript`; push/verify.
- `OP_CHECKSIGADD`: three elements, `num = CScriptNum(stacktop(-2))` (4 bytes), `EvalChecksig`, push
  `num + success` (may be 5 bytes). Lean `pubkey :: numv :: sig :: rest`, `toNum false 4`, `serialize`.
- `OP_CHECKMULTISIG(VERIFY)` → `TAPSCRIPT_CHECKMULTISIG` inside the `case` (executed only). Lean: `none`
  in `tapExecOp`, which is reached only when `fExec` (not in the `IF..ENDIF` range).
- `OP_CODESEPARATOR`: `m_codeseparator_pos = opcode_pos`, where `opcode_pos` is incremented by the `for`
  header for every `GetOp` (executed or not, push or not). Lean: `codeseparatorPos := ts.opcodePos`,
  `opcodePos + 1` in both `tapStep` branches. The sighash reads the position at the time of the check
  (`ed' := {ed with codeseparatorPos := ts.codeseparatorPos}`).
- `EvalChecksigTapscript`: `success = !sig.empty()`; if so `weight −= 50`, `< 0 → fail`; empty pubkey
  → fail; 32 bytes → check iff `success`; else policy only. Lean identical, same order.
- Unknown opcodes `0xff` (not a success opcode) fail only when executed; `OP_VERIF`/`OP_VERNOTIF` fail
  when skipped; disabled opcodes are all success opcodes (never reached). Same in both.

## Vectors

`tests/reference/second_taproot_reference.py` (imports the C++-derived machinery of
`second_script_reference.py`: BIP340 signing, taproot tweaks, a Merkle tree builder, the BIP341 sighash
and the full `VerifyWitnessProgram`/`ExecuteWitnessScript` transcription) generates
`tests/SecondReviewTaprootVectors.lean`: 115 lines (`taprootHandler`, `verifyScriptFull`,
`sigHashSchnorr`) over a two-input one-output transaction. Coverage: key path with hash types 0, 1,
2, 0x81, 0x82, sizes 63/66, hash types 0x04/0x80/explicit 0x00, DEFAULT vs ALL, the internal key as
program, input 1 with ANYONECANPAY, `SINGLE`/`SINGLE|ANYONECANPAY` at input 1 (no output); the annex
(`[50]`, `[50,00]`, empty last element, `[51]`, a lone `0x50…` element, an annex-looking element not
last, script path with a 20-byte annex committed/not committed/absent); control sizes 32/33/34, an
invalid internal x, another internal key, the parity bit, a changed script, another output's program,
a 128-node path (4129 bytes) against 129 (4161) and 127 nodes; leaf versions `0xc2` with an unparsable
script and `0xfe`, each reclaimed as `0xc0`; `OP_SUCCESS80` skipped, before/after a truncated push, with
1200 witness elements and with a 1000-byte element, `0xff` skipped/executed, `OP_VERIF` skipped; 300
NOPs and 250 code separators; 999/1000/1001 initial elements; 520/521-byte elements; `MINIMALIF` on
`[]`, `[01]`, `[02]`, `[00]`, `[01,00]`, `[80]` and the empty stack with `OP_NOTIF`; code-separator
positions 2 (after `OP_1 OP_DROP`), skipped, doubled, after the check; `OP_CHECKSIGADD` with
`2^31−1 + 1` compared bytewise, a 5-byte `n`, valid/empty/wrong/zero/1-byte signatures, a 33-byte key
with a 1-byte and an empty signature, an empty key, an invalid-x key with an empty and a 64-byte
signature, two elements; `OP_CHECKSIG` with a 33-byte key; `OP_CHECKSIGVERIFY`; `OP_CHECKMULTISIG`
executed/skipped; the weight budget at 10/11 checks, the same 11 checks rescued by a 21-byte annex, 13
unchecked (33-byte key) signatures over budget and 5 within, 30 `CHECKSIGADD`s with empty signatures;
`verifyScriptFull` key/script path, non-empty scriptSig, empty witness, P2SH-wrapped; `sigHashSchnorr`
at input 1 for hash types 0/1/3/0x83 (the last two `none`) and a Tapscript hash with code-separator
position 7. Run in `/root/prove2me_workspace`: `sort | uniq -c` → `115 true`.

## Checks from the guide

1. **Order of tests.** Annex before the key-path/script-path split; control size before the leaf hash
   and the commitment; the `OP_SUCCESSx` scan before the stack and element limits; weight before the
   empty-pubkey test; `num` parsed before the signature in `CHECKSIGADD`. Same order; where it differs
   (pure functions) no verdict changes.
2. **Constants.** `0x50`, 50/50, 33/32/128/4129, `0xfe`/`0xc0`, 32-byte program, 1000, 520, the
   hash-type set: equal.
3. **Integer semantics.** `control.length − 33` guarded; `weightLeft : Int` with `< 0` as the int64
   test; `hashType &&& 3`, `&&& 0x80` on `Nat`; `tx.version` is `uint32_t` in this revision, so the
   `Nat` serialization is right.
4. **Defaults on degenerate input.** `tx.vin.getD inPos` / `spent.getD inPos` are behind Core's
   asserts (`in_pos < vin.size()`, spent outputs one per input); `stack.getD 0 []` is under
   `stack.length = 1`; `top.getD 0 0` is under `top.length = 1`.
5. **Policy vs consensus.** `DISCOURAGE_OP_SUCCESS`, `DISCOURAGE_UPGRADABLE_PUBKEYTYPE`,
   `DISCOURAGE_UPGRADABLE_TAPROOT_VERSION` absent; `MINIMALIF` present only under Tapscript;
   `MINIMALDATA` (the `fRequireMinimal` of `CHECKSIGADD`'s `num`) absent. Correct.
