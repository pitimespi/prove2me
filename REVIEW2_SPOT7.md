# Second review, spot 7: `Def_BitcoinVerify` against `VerifyScript`

Independent second review (the first reviewer's reports were not read). Core revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`.

Core:
- `VerifyScript`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L2012-L2112
- `VerifyWitnessProgram`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1927-L2010
- `ExecuteWitnessScript`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1842-L1880
- `EvalScript` head (`MAX_SCRIPT_SIZE`, `GetOp`): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L417-L460
- `CScript::IsPayToAnchor` / `IsPayToScriptHash` / `IsWitnessProgram` / `IsPushOnly` / `GetScriptOp`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.cpp#L207-L361
- `CheckSignatureEncoding`, `CheckECDSASignature`, `SignatureHash`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L211-L237, L1610-L1725
- `GetBlockScriptFlags`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249-L2288

Lean: `/home/user/prove2me/Definitions/Def_BitcoinVerify.lean` (`evalBytes`, `isPayToScriptHash`,
`isWitnessProgram`, `isPushOnly`, `isPayToAnchor`, `topTrue`, `executeWitnessScriptV0`, `p2wpkhExec`,
`verifyWitnessProgram`, `verifyScript`). Blind read-back used:
`scratchpad/audit12/readback_Def_BitcoinVerify.md` (present; matches the Lean as read here, and
already notes that "the script code is always the whole script").

## Verdict

**No defect in the dispatch layer; the two script-code defects of spot 1 are observable here.**
`verifyScript`, `verifyWitnessProgram`, `executeWitnessScriptV0`, `isWitnessProgram`, `isPushOnly`,
`isPayToScriptHash` and `isPayToAnchor` transcribe Core exactly: the scriptSig/scriptPubKey evaluation on
one stack, the `stackSig` copy restored for P2SH (the P2SH flag gates both the copy and the branch),
the consensus push-only test for P2SH (and no `SIGPUSHONLY`), the empty-scriptSig rule for native
programs, the single-canonical-push rule for wrapped programs (`scriptSig = pushBytes redeem`,
byte-exact), `WITNESS_UNEXPECTED` when no program was seen and the witness is non-empty (also for an
empty-element witness, and not when the `WITNESS` flag is off), unknown versions / version 1 with a
non-32-byte program / P2SH-wrapped version 1 / pay-to-anchor all succeeding (the `DISCOURAGE_*` flags
being policy), the `TAPROOT` flag gating the handler, the 520-byte test on the witness elements with
the P2WSH script exempt, `MAX_SCRIPT_SIZE` on the witness script through `evalBytes`, no
`CLEANSTACK` outside `ExecuteWitnessScript` and the exact-one-true-element rule inside it, the
P2WPKH script `DUP HASH160 <20> EQUALVERIFY CHECKSIG` with two witness items, P2WSH's last element
and SHA-256 test, `DERSIG` as the only signature-encoding flag (high-S, undefined hash types,
uncompressed and hybrid keys accepted; the SIGHASH_SINGLE "hash 1" bug reproduced). The only
verdict-changing differences are inherited from `evalBytes` fixing the signature script code to the
whole script: an executed `OP_CODESEPARATOR` that is not the first instruction (legacy) or any
executed `OP_CODESEPARATOR` (witness v0), and `CHECKMULTISIG` with another signature's push inside the
script code; concrete inputs and directions are in REVIEW2_SPOT1.md and in sections 4–5 of
`tests/SecondReviewVerifyVectors.lean` (six lines marked `CORE:` print `false`).

## `VerifyScript` ↔ `verifyScript`

| Core | Lean |
|---|---|
| `SIGPUSHONLY` (policy) | absent |
| `EvalScript(stack, scriptSig, BASE)`; fail → false | `evalBytes c .base [] scriptSig`; `none → false` |
| `if (P2SH) stackCopy = stack` | `stackSig` kept (used only under `c.flags.p2sh`) |
| `EvalScript(stack, scriptPubKey)`; empty or false top → `EVAL_FALSE` | `evalBytes c .base stackSig scriptPubKey`; `!topTrue stack → false` |
| `WITNESS && IsWitnessProgram(scriptPubKey)`: `scriptSig.size() != 0 → MALLEATED`; `VerifyWitnessProgram(is_p2sh=false)`; `stack.resize(1)`; `hadWitness` | `native := some (scriptSig = [] && verifyWitnessProgram … false)`; returns it directly (a scriptPubKey cannot be both a witness program and P2SH; `hadWitness` makes the final test a no-op) |
| `P2SH && IsPayToScriptHash`: `!IsPushOnly(scriptSig) → SIG_PUSHONLY`; `swap(stack, stackCopy)`; `pubKey2 = back; pop`; `EvalScript(pubKey2)`; empty/false → `EVAL_FALSE` | same on `stackSig`: `redeem :: rest`, `evalBytes c .base rest redeem`, `topTrue stack2` |
| `WITNESS && IsWitnessProgram(pubKey2)`: `scriptSig != CScript() << pubKey2 → MALLEATED_P2SH`; `VerifyWitnessProgram(is_p2sh=true)` | `scriptSig ≠ pushBytes redeem → false`; `verifyWitnessProgram … true` |
| `CLEANSTACK` (policy) | absent |
| `WITNESS && !hadWitness && !witness.IsNull() → WITNESS_UNEXPECTED` | the two `c.flags.witness && !witness.isEmpty → false` arms (non-P2SH, and P2SH with a non-program redeem) |

`pushBytes` matches `CScript::operator<<(vector)` (direct push below 0x4c, `PUSHDATA1` ≤ 0xff,
`PUSHDATA2` ≤ 0xffff, else `PUSHDATA4`); a redeem script of 4..42 bytes is always a direct push, so
`PUSHDATA1`/`PUSHDATA2` encodings of it fail the single-push rule as in Core (vectors).

## `VerifyWitnessProgram` ↔ `verifyWitnessProgram`

Version 0, 32 bytes: empty witness → fail; last element is the script; `SHA256(script) = program`;
`ExecuteWitnessScript(rest, WITNESS_V0)`. Lean: `witness.getLast?`, `BitcoinSer.sha256 script ≠ program`,
`executeWitnessScriptV0 c witness.dropLast.reverse script` (top-first conversion correct). Version 0,
20 bytes: exactly 2 items; `DUP HASH160 <program> EQUALVERIFY CHECKSIG` (`p2pkhBytes` builds the same
26 bytes). Other version-0 lengths: fail. Version 1, 32 bytes, not P2SH: `TAPROOT` flag off → true,
else the handler. `!is_p2sh && IsPayToAnchor` → true; otherwise true. All match. The `taproot` flag is
the only flag read here, as in Core.

## `ExecuteWitnessScript` (v0) ↔ `executeWitnessScriptV0`

Core: elements > 520 → `PUSH_SIZE`; `EvalScript` (which applies `MAX_SCRIPT_SIZE` and the op count
for v0); `stack.size() != 1 → CLEANSTACK`; `!CastToBool(back) → EVAL_FALSE`. Lean: `stack.any (520 <)`,
`evalBytes c .witnessV0`, `st.length = 1 && topTrue st`. Match. There is no initial 1000-element test
for v0 in either (vectors: 1001 initial elements fail only after the first instruction).

## `IsWitnessProgram` / `IsPayToScriptHash` / `IsPushOnly` / `IsPayToAnchor`

`isWitnessProgram`: `4 ≤ len ≤ 42`, first byte `OP_0` or `OP_1..OP_16`, `s[1] + 2 = len` → `(DecodeOP_N,
program)`; `decodeOpN` is `b - 0x50` for the `OP_n` bytes. `isPayToScriptHash`: exactly 23 bytes,
`0xa9 0x14 … 0x87`. `isPushOnly`: every instruction parses and its opcode is ≤ `OP_16`
(`OP_1NEGATE`, `OP_RESERVED`, `OP_n` count as pushes, as in Core). `isPayToAnchor version program`:
`version = 1 ∧ program = [0x4e, 0x73]`. All match `script.cpp`.

## `evalBytes` and the signature context

`evalBytes`: `10000 < script.length → none` (Core: `> MAX_SCRIPT_SIZE`, BASE and WITNESS_V0 only —
`evalBytes` is only used for those two), `parseScript` (a malformed push fails the whole evaluation;
equivalent to Core's in-loop `BAD_OPCODE` because the loop has no successful early exit), then
`BitcoinScript.evalScript` with `legacyOracle (sigFlagsOf flags) tx nIn amount v script`.
`sigFlagsOf` forwards `DERSIG` only (correct: `LOW_S`, `STRICTENC`, `WITNESS_PUBKEYTYPE` are policy).
The script code handed to the oracle is the whole `script`: this is where the two spot-1 defects
become observable (`OP_CODESEPARATOR` position; per-signature `FindAndDelete` in `CHECKMULTISIG`).

## Vectors

`tests/reference/second_verify_reference.py` (imports the C++-derived machinery of
`second_script_reference.py`; pure-Python secp256k1, ECDSA signing, DER, lax DER parsing, legacy and
BIP143 sighashes) generates `tests/SecondReviewVerifyVectors.lean`: 93 `verifyScript` lines over a
two-input one-output transaction with real signatures. Coverage: high-S, hash types 0x00/0x05/0xff,
`ALL|ANYONECANPAY`, `NONE`; a padded-R signature rejected under `DERSIG` and accepted without it; a
69-byte signature; an empty signature; an invalid 1-byte pubkey with a DER signature (false, no
error); uncompressed and hybrid keys (legacy and P2WPKH); the SIGHASH_SINGLE bug at input 1 (and its
absence under BIP143); `OP_CODESEPARATOR` first/middle/skipped (legacy) and in P2WSH; `CHECKMULTISIG`
with a signature push inside the script code; P2SH-P2WPKH with canonical, `PUSHDATA1`, `PUSHDATA2`,
doubled and `OP_NOP`-suffixed scriptSigs; P2SH-wrapped v1/v2/anchor with empty or oversized witnesses;
the stack copy; `CLEANSTACK` absence; `WITNESS_UNEXPECTED` with an empty-element witness; 10000 vs
10001-byte witness scripts; 520/521-byte pushes inside and elements outside the script; `MINIMALIF`
absence in v0; the op count in v0; 1001-element witness stacks; P2WPKH item counts and swaps;
`IsWitnessProgram` boundaries (3, 4, 42, 43 bytes, `OP_RESERVED`, `OP_1NEGATE`, `PUSHDATA1` form,
all-zero programs failing as plain scripts); P2SH recognition (24 bytes, `PUSHDATA1` form,
`OP_EQUALVERIFY`). Run in `/root/prove2me_workspace`: `sort | uniq -c` → `87 true`, `6 false`. The
six `false` lines are exactly the ones marked `CORE:`; each asserts the Core verdict (checked by the
Python transcription with an `assert`) and the model's verdict is the opposite — this is defect (1)
and (2) of REVIEW2_SPOT1.md, not a reference error. All other 87 lines agree.

## Checks from the guide

1. **Order of tests.** Native witness before P2SH (disjoint anyway); push-only before the restore; the
   malleability tests before `VerifyWitnessProgram`; `WITNESS_UNEXPECTED` last. Same order, same
   verdicts.
2. **Constants.** 10000, 20/32/32 program sizes, 23-byte P2SH, 4..42-byte programs, `0x4e73`: equal.
3. **Integer semantics.** `decodeOpN` truncated subtraction unreachable (first byte already
   restricted); `s.getD 1 0 + 2 = s.length` on `Nat` is exact for lengths ≥ 4; `amount : Int` with the
   `-1` sentinel matches `CAmount`.
4. **Defaults on degenerate input.** `stackSig = []` in the P2SH branch is unreachable (Core asserts);
   `witness.getLast?` on `[]` gives the `WITNESS_EMPTY` failure; `topTrue []` is `EVAL_FALSE`.
5. **Policy vs consensus.** `SIGPUSHONLY`, `CLEANSTACK`, `MINIMALIF`, `WITNESS_PUBKEYTYPE`,
   `DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM`, `DISCOURAGE_UPGRADABLE_TAPROOT_VERSION`, `LOW_S`,
   `STRICTENC`, `NULLFAIL` are all absent; `P2SH`, `WITNESS`, `TAPROOT`, `DERSIG`, CLTV, CSV,
   `NULLDUMMY` are carried from `BitcoinActivation.ScriptFlags`. Correct.
