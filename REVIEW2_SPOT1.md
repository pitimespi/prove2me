# Second review, spot 1: `Def_BitcoinScript` against `EvalScript`

Independent second review (the first reviewer's reports were not read). Core revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`.

Core:
- `EvalScript` (BASE / WITNESS_V0 / TAPSCRIPT): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L417-L1249
- `CastToBool`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L46-L58
- `EvalChecksigPreTapscript` (FindAndDelete, encoding checks, NULLFAIL): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L331-L355
- `FindAndDelete`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L239-L263
- `CheckLockTime` / `CheckSequence`: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1755-L1830
- `CScriptNum` (`script.h`): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h#L227-L395
- constants (`script.h`): `MAX_SCRIPT_ELEMENT_SIZE` L29, `MAX_OPS_PER_SCRIPT` L32, `MAX_PUBKEYS_PER_MULTISIG` L35, `MAX_SCRIPT_SIZE` L41, `MAX_STACK_SIZE` L44, `LOCKTIME_THRESHOLD` L48
- `GetBlockScriptFlags` (the mainnet flag set): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249-L2288

Lean: `/home/user/prove2me/Definitions/Def_BitcoinScript.lean` (`toNum`, `serialize`, `castToBool`,
`execOp`, `step`, `run`, `evalScript`, `multisigLoop`), and the concrete oracle it is run with,
`BitcoinSig.legacyOracle` / `checkSigPreTapscript` in `Definitions/Def_BitcoinSig.lean` (read for the
signature-context checks only). Blind read-back used:
`scratchpad/audit9/readback_Def_BitcoinScript.md` (present; its description matches the Lean as read here).

## Verdict

**Defect found (two, both at the signature-context boundary; everything on the stack machine itself
matches).** (1) `OP_CODESEPARATOR` is a no-op in `execOp` and the `Oracle` has no notion of a code
position, so every `CHECKSIG`/`CHECKMULTISIG` is checked against the *whole* script, whereas Core
checks against the script from the last *executed* `OP_CODESEPARATOR` (`pbegincodehash`). For the legacy
sighash the serializer strips remaining separators, so the two agree when every instruction before
the last executed separator is itself a separator; they differ otherwise, and for witness v0 (BIP143
keeps separator bytes and only cuts at `pbegincodehash`) they differ for any executed separator.
Concrete input (vectors in `tests/SecondReviewVerifyVectors.lean`, section 4): scriptPubKey
`<pk> OP_CODESEPARATOR OP_CHECKSIG`, scriptSig `<sig>` where `sig` signs the script code `OP_CHECKSIG`
— Core: true, model: false (model stricter); with `sig` over the whole script — Core: false, model:
true (model more lenient). P2WSH `OP_CODESEPARATOR <pk> OP_CHECKSIG` behaves the same way. (2)
`OP_CHECKMULTISIG` in Core runs `FindAndDelete` for *every* signature on the stack before any check;
the Lean `multisigLoop` calls the oracle per `(sig, key)` pair and `checkSigPreTapscript` deletes only
that one signature. Concrete input (section 5 of the same vectors): scriptPubKey
`<sigB> OP_DROP OP_2 <pkA> <pkB> OP_2 OP_CHECKMULTISIG`, scriptSig `OP_0 <sigA> <sigB>` with `sigB`
over the code with `<sigB>` deleted: `sigA` over that same deleted code — Core: true, model: false
(stricter); `sigA` over the undeleted scriptPubKey — Core: false, model: true (more lenient). Both
defects are documented in passing in the `legacyOracle` docstring ("for scripts without
`OP_CODESEPARATOR`") but are not among the accepted limits of the brief. Everything else checked —
the full opcode table and stack effects, `CScriptNum` (4 bytes in, 5 for CLTV/CSV, unbounded out,
negative zero, padding accepted since `MINIMALDATA` is policy), the operation count (opcodes above
`OP_16`, counted before execution and in skipped branches, `+nKeys` for multisig, limit 201), the
stack+altstack limit of 1000 after every instruction including skipped ones, the 520-byte push limit
also in skipped branches, the disabled opcodes in skipped branches, `OP_VERIF`/`OP_VERNOTIF` failing
when skipped and `OP_RESERVED`/`OP_VER`/`OP_CHECKSIGADD`/unknown opcodes failing only when executed,
the condition stack, `NULLDUMMY`, the multisig key/signature ordering and early exit, CLTV/CSV with
the real checker semantics, `CastToBool` — matches Core.

## `CScriptNum` ↔ `toNum` / `serialize` / `setVch`

Core: the constructor throws if `vch.size() > nMaxNumSize` (4 by default, 5 for CLTV/CSV); with
`fRequireMinimal` (policy, `MINIMALDATA`) a non-minimal encoding throws; `set_vch` reads little-endian
with the top bit of the last byte as sign; `serialize` writes the magnitude little-endian and either
appends `0x80`/`0x00` or sets the top bit; `getint()` clamps to `int`.
Lean: `toNum requireMinimal maxSize v` is `none` when `maxSize < v.length` or (minimal and non-minimal),
else `setVch`; `serialize` identical; no `getint` clamp (unreachable with ≤ 4-byte operands). Results
of arithmetic are pushed unbounded (`pushNum`), so 5-byte results such as `2^31` are produced and
rejected as later operands, as in Core.

## `CastToBool` ↔ `castToBool`

Core: some byte non-zero, except a trailing `0x80` after zeros. Lean: structurally the same
(`[0x80,0]` true, `[0,0x80]` false). Match.

## `EvalScript` loop ↔ `step` / `run`

| Core | Lean |
|---|---|
| `script.size() > MAX_SCRIPT_SIZE` (BASE/V0) | not here; `BitcoinVerify.evalBytes` tests `10000 < length` before parsing (spot 7) |
| `GetOp` failure → `BAD_OPCODE` | `BitcoinSig.parseScript` fails up front; equivalent since the loop has no successful early exit |
| `vchPushValue.size() > 520` → `PUSH_SIZE`, before `fExec` is consulted | `step (.push d)`: `520 < d.length → none` before the `allTrue` test |
| `opcode > OP_16 && ++nOpCount > 201` (BASE/V0 only, before the disabled test, regardless of `fExec`) | `counted := OP_16 < c`; `201 < opCount + 1 → none`, then increment; same order |
| disabled opcodes → `DISABLED_OPCODE` regardless of `fExec` | `isDisabled c → none` after the count, before `fExec` |
| `OP_CODESEPARATOR` + `CONST_SCRIPTCODE` (policy) | absent, correct |
| push executed only if `fExec`; `switch` entered if `fExec` or `OP_IF ≤ op ≤ OP_ENDIF` | identical gate; `OP_VERIF`/`OP_VERNOTIF` (0x65/0x66) hit the catch-all → fail even when skipped |
| `stack.size() + altstack.size() > 1000` after every iteration | after every `step`, in all three branches (push, executed/conditional op, skipped op) |
| `!vfExec.empty()` at the end → `UNBALANCED_CONDITIONAL` | `run _ [] = if vfExec.isEmpty then some s else none` |

`ConditionStack`: Core stores size + first-false position; `toggle_top` flips the top. The Lean list of
booleans with `allTrue = all id` and `(!b) :: rest` is observationally identical (toggling a non-first
false is invisible to `all_true` in both).

## The opcode table (`execOp`)

Checked case by case against the `switch`: `OP_1NEGATE`/`OP_1..OP_16` push `opcode - (OP_1 - 1)`;
`OP_NOP`; CLTV/CSV (flag off → NOP; empty stack → fail; 5-byte number; negative → fail; CSV disable
bit → NOP; checker); `OP_NOP1`,`OP_NOP4..10` (DISCOURAGE flag is policy); `OP_IF`/`OP_NOTIF` (pop and
push only when `fExec`, else push `false`; `MINIMALIF` is policy for v0 and absent here — the Tapscript
rule lives in `Def_BitcoinTaproot`); `OP_ELSE`/`OP_ENDIF`; `OP_VERIFY`; `OP_RETURN`; the 19 stack
operations with the top-first convention (2OVER, 2ROT, 2SWAP, ROT, TUCK, NIP, OVER, PICK/ROLL with
`n < 0 || n >= size` after the pop); `OP_SIZE`; `OP_EQUAL(VERIFY)` bytewise; the six unary and
thirteen binary numeric opcodes with `bn1 = stacktop(-2)`, `bn2 = stacktop(-1)`; `OP_WITHIN` as
`min ≤ x < max`; the five hashes through the oracle; `OP_CHECKSIG(VERIFY)` with sig below pubkey;
`OP_CHECKSIGADD` → `BAD_OPCODE` in BASE (catch-all); `OP_CHECKMULTISIG(VERIFY)`: `nKeys ∈ [0,20]`,
`opCount += nKeys ≤ 201`, keys top-first, `nSigs ∈ [0,nKeys]`, sigs top-first, matching loop with
early exit when `nSigs > nKeys` (later encoding failures unobserved), dummy required, `NULLDUMMY`;
`default → BAD_OPCODE` ↔ `else none` (covers `OP_RESERVED`, `OP_VER`, `OP_RESERVED1/2`, `0xba..0xff`).
All match except the two signature-context points of the verdict.

## `multisigLoop` and the oracle

Core (BASE): `scriptCode = [pbegincodehash, pend)`; `for each of the nSigs signatures:
FindAndDelete(scriptCode, CScript() << sig)` (all deleted first); then the loop checks
`CheckSignatureEncoding` (DERSIG on mainnet), `CheckPubKeyEncoding` (policy only) and
`CheckECDSASignature(sig, key, scriptCode)` for the examined pairs only.
Lean: `multisigLoop o sigs keys` calls `o.checkSig sig key` per examined pair; with `legacyOracle`,
`checkSigPreTapscript` deletes the push of *that* signature only, from the *whole* script. Defect (2)
of the verdict; invisible unless the script code contains a push of one of the other signatures.

## `OP_CODESEPARATOR`

Core: `pbegincodehash = pc` (after the separator) when executed; the sighash uses the script from
there. Lean: `some s`; the oracle's `scriptCode` is fixed to the whole script by `BitcoinVerify.evalBytes`.
Defect (1) of the verdict. (The op count and stack effects of the separator are right.)

## Vectors

`tests/reference/second_script_reference.py` (written from the C++ only; the interpreter, `CScriptNum`,
`CheckLockTime`/`CheckSequence`, `VerifyScript`, the sighashes and the taproot helpers all live there and
are shared by spots 7 and 8) generates `tests/SecondReviewScriptVectors.lean`: 253 `#eval … == …`
lines on parsed instructions against an abstract oracle (hashes prefix a tag byte, `checkSig` fails the
script for `[0xff]` and succeeds iff `sig = pubkey + 2`, lock-time checks are the real
`BitcoinSig.checkLockTime/checkSequence` over four transactions). Coverage: empty/short-stack
behaviour of every operand-taking opcode; skipped vs executed failure of `OP_RESERVED`, `OP_VER`,
`OP_RESERVED1/2`, `OP_CHECKSIGADD`, `0xbb`, `0xff`, `OP_VERIF`, `OP_VERNOTIF`, all fifteen disabled
opcodes, `OP_RETURN`, `OP_VERIFY`; 520/521-byte pushes in skipped branches; the 1000-element limit with
skipped instructions, the altstack and initial stacks of 1001/1002 elements; the op count including
skipped opcodes, `OP_0`/`OP_1NEGATE`/`OP_16` not counted, multisig key counts across two
`CHECKMULTISIG`s; 5-byte arithmetic results, padded and negative-zero operands, 5-byte operands
rejected, every comparison opcode; `PICK`/`ROLL` indices (padded, `-0`, out of range, 5-byte); stack
shuffles; `NOTIF`, nesting, double/triple `ELSE`, unbalanced conditionals; `CHECKSIG` outcomes;
`CHECKMULTISIG` 0-of-0, negative counts, padded counts, ordering, early exit before an encoding failure
is examined, the dummy and `NULLDUMMY` on/off, 20 vs 21 keys; CLTV (threshold types, equality, `+1`,
final input, negative, `-0`, 5-byte `2^32`, flag off) and CSV (height/time types, mask, disable bit on
the operand and on the input, version 1, 6-byte operand, flag off). Run in
`/root/prove2me_workspace`: `sort | uniq -c` → `253 true`. (An earlier run showed 31 `false`
lines, all caused by my generator rendering `OP_0` as `.op 0x00` instead of `.push []`; fixed in the
generator, not a Lean issue.)

The two defects are exercised with real ECDSA signatures through `verifyScript` in
`tests/SecondReviewVerifyVectors.lean` (sections 4 and 5), where the six lines marked `CORE:` assert
Core's verdict and print `false` against the model.

## Checks from the guide

1. **Order of tests.** Push size → op count → disabled → execute, as in Core; the count precedes the
   disabled test (a 202nd disabled opcode fails either way); the stack limit is tested after every
   instruction. `PICK`/`ROLL` test the stack depth before parsing the index; multisig tests the dummy
   after the matching loop. No order difference changes a verdict.
2. **Constants.** 520, 201, 20, 1000, 4/5-byte numbers, `2^31` disable flag: all equal to `script.h`.
3. **Integer semantics.** `CScriptNum` is `Int` with the exact byte codec; no truncation; `getint`
   clamping unreachable; `n.toNat &&& DISABLE_FLAG` safe because `n ≥ 0` was tested first.
4. **Defaults on degenerate input.** `eraseAt` out of range unreachable (guarded); `rest[i]?` guarded;
   `toNum` on empty gives 0 as `set_vch`; `allTrue [] = true` as `all_true()` on an empty stack.
5. **Policy vs consensus.** `Flags` carries exactly CLTV/CSV/NULLDUMMY (the interpreter-level consensus
   flags on mainnet); `MINIMALDATA`, `NULLFAIL`, `CONST_SCRIPTCODE`, `DISCOURAGE_UPGRADABLE_NOPS`,
   `MINIMALIF` (v0), `STRICTENC`, `LOW_S`, `WITNESS_PUBKEYTYPE` are correctly absent. `DERSIG` is
   applied inside the oracle (spot 7). The two defects are fidelity gaps of the consensus script code,
   not policy confusions.
