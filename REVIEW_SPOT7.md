# Spot 7: `VerifyScript`, `VerifyWitnessProgram`, `ExecuteWitnessScript` versus `BitcoinVerify`

Core: [`interpreter.cpp:2012`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L2012)
(`VerifyScript`), [`:1927`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1927)
(`VerifyWitnessProgram`), [`:1842`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1842)
(`ExecuteWitnessScript`), [`script.cpp:224`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.cpp#L224)
(`IsPayToScriptHash`, `IsWitnessProgram`, `IsPushOnly`, `IsPayToAnchor`). Lean: `Definitions/Def_BitcoinVerify.lean`.
Read-back: `missions/readbacks/verify/readback_Def_BitcoinVerify.md`.

## Verdict

Agreement on the control flow, the three malleability rules, the upgrade hooks and the predicates.
The Lean returns early in two places where Core falls through; both are shown below to be
equivalent. Policy flags `SIGPUSHONLY` and `CLEANSTACK` are off.

## `VerifyScript` — `verifyScript`

| Core | Lean | Agree |
|---|---|---|
| `SIGPUSHONLY` | policy, off | yes |
| `EvalScript(scriptSig)`; `stackCopy = stack` if `P2SH`; `EvalScript(scriptPubKey)` on the same stack; empty or false top → `EVAL_FALSE` | `evalBytes` twice (each with the 10,000-byte test and the parse), `topTrue` | yes |
| with `WITNESS`: if the output is a witness program, `hadWitness`; non-empty scriptSig → `WITNESS_MALLEATED`; `VerifyWitnessProgram(is_p2sh = false)` fails → false; `stack.resize(1)`; **then fall through** to the P2SH test, `CLEANSTACK`, and the final `hadWitness` test | returns the program's verdict immediately | yes: a witness program (`OP_n` then one push, 4–42 bytes) is never `IsPayToScriptHash` (23 bytes starting `0xa9`), `CLEANSTACK` is off, and `hadWitness` is true, so nothing after the fall-through can change the verdict |
| with `P2SH` and a P2SH output: scriptSig not push-only → fail; restore `stackCopy`; `assert(!stack.empty())`; pop the redeem script; `EvalScript(redeem)` on the rest; empty or false top → fail | `isPushOnly`; `match stackSig with [] => false \| redeem :: rest`; `evalBytes`; `topTrue` | yes: the assert is unreachable because an empty push-only scriptSig leaves an empty stack on which `OP_HASH160` already failed, which the Lean reports as `false` through the same path |
| then with `WITNESS`: if the redeem script is a witness program, `hadWitness`; scriptSig must equal `CScript() << redeem` (the canonical push) → else `WITNESS_MALLEATED_P2SH`; `VerifyWitnessProgram(is_p2sh = true)`; `stack.resize(1)`; fall through | `scriptSig ≠ pushBytes redeem → false`; returns the program's verdict | yes: `hadWitness` is true so the final test passes; `CLEANSTACK` off |
| `CLEANSTACK` | policy, off | yes |
| with `WITNESS`: `!hadWitness ∧ !witness.IsNull()` → `WITNESS_UNEXPECTED` | the two `if c.flags.witness && !witness.isEmpty then false` branches (after a plain output, and after a P2SH redeem that is not a witness program) | yes |

## `VerifyWitnessProgram` — `verifyWitnessProgram`

| Core | Lean | Agree |
|---|---|---|
| v0, 32-byte program: empty witness → fail; the last element is the script; `SHA256(script) ≠ program` → fail; `ExecuteWitnessScript` on the remaining elements, `WITNESS_V0` | `witness.getLast?`; `sha256 script ≠ program`; `executeWitnessScriptV0 c witness.dropLast.reverse script` (top-first) | yes |
| v0, 20-byte program: exactly two elements; the implied `DUP HASH160 <program> EQUALVERIFY CHECKSIG` | `witness.length ≠ 2 → false`; `p2wpkhExec = p2pkhBytes program` | yes |
| v0, other size → `WRONG_LENGTH` | `false` | yes |
| v1, 32 bytes, not P2SH: `TAPROOT` off → success; else the Taproot branch (spot 8) | `if !c.flags.taproot then true else tap c witness program` | yes |
| `!is_p2sh ∧ IsPayToAnchor` → true; everything else (unknown versions, P2SH-wrapped v1, v1 with other sizes) → true (`DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM` is policy) | `true` in both branches | yes |

## `ExecuteWitnessScript`, `SigVersion::WITNESS_V0` — `executeWitnessScriptV0`

Every element at most 520 bytes; `EvalScript` under `WITNESS_V0` (the Script mission's interpreter
with the v0 oracle: no `FindAndDelete`, BIP143 sighash); exactly one element left; `CastToBool` of
it. The `MAX_STACK_SIZE` test on the initial stack is Tapscript-only in Core and is likewise absent
here. Identical.

## Predicates

`IsPayToScriptHash` (23 bytes, `a9 14 … 87`), `IsWitnessProgram` (4–42 bytes, `OP_0` or
`OP_1..OP_16`, `sig[1] + 2 = size`, version by `DecodeOP_N`), `IsPushOnly` (every `GetOp` succeeds
and every opcode is at most `OP_16`, so `OP_1NEGATE`, `OP_RESERVED` and `OP_n` count as pushes),
`IsPayToAnchor(version, program)` (`version = 1`, program `4e 73`): identical.

## Vectors (`tests/VerifyVectors.lean`)

The 20 earlier dispatch cases plus 38 adversarial ones: P2WSH with a clean and an unclean stack,
hash mismatch, empty witness, a 521-byte versus a 520-byte element, a script leaving `false` or
nothing; v0 with a 25-byte program; P2WPKH with three elements and with an empty signature; unknown
version 16, v1 with a 20-byte program, pay-to-anchor, P2SH-wrapped v1 (handler never consulted),
native v1 with the flag on and off; the three malleability rules (extra push or `OP_1` in a wrapped
scriptSig, non-empty native scriptSig); P2SH with an empty scriptSig, the restored stack with and
without an extra push, a redeem script needing the pushed argument, `OP_1` allowed and `OP_NOP`
rejected as push-only; each flag off in turn; and the 10,000-byte and 201-operation limits reached
through `evalBytes`. All agree.
