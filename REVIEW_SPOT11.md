# Spot 11: sigop accounting versus `BitcoinBlockV2.getSigOpCount`, `p2shSigOpCount`, `countWitnessSigOps`, `txSigOpCost`

Core: [`script.cpp:159`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.cpp#L159)
(`CScript::GetSigOpCount(bool)`), [`:183`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.cpp#L183)
(`CScript::GetSigOpCount(const CScript&)`), [`tx_verify.cpp:118`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L118)
(`GetLegacySigOpCount`), [`:132`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L132)
(`GetP2SHSigOpCount`), [`:149`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L149)
(`GetTransactionSigOpCost`), [`interpreter.cpp:2133`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L2133)
(`WitnessSigOps`, `CountWitnessSigOps`).

## Verdict

One defect found and fixed (F1). Everything else agrees.

**F1 (defect, fixed in this repository).** `GetP2SHSigOpCount` adds
`prevout.scriptPubKey.GetSigOpCount(scriptSig)` *only for inputs whose spent output is P2SH*. The
Lean `txSigOpCost` summed `p2shSigOpCount spk scriptSig` over every input, and `p2shSigOpCount`
transcribed the *method* `CScript::GetSigOpCount(const CScript&)`, whose non-P2SH branch returns the
accurate count of the script itself. So for every non-P2SH spent output the model added that
output's own `CHECKSIG`s, weighted by 4, to the transaction's cost: a plain P2PKH spend cost 8
instead of 4. The model was therefore *stricter* than Core: it could reject a block whose true
cost is within 80,000 while the model's count exceeds it (a block spending many P2PKH outputs near
the limit); it could never accept a block Core rejects. The fix makes `p2shSigOpCount` the per-input
term of `GetP2SHSigOpCount` (`0` unless the spent output is P2SH). No theorem statement mentions the
function; all nineteen proofs re-check unchanged. The definition published on the platform as
mission 13's `BitcoinBlock` still contains the old text and needs a revision.

How it was found: by reading `GetP2SHSigOpCount`'s `if (prevout.scriptPubKey.IsPayToScriptHash())`
against the Lean sum, then confirming by evaluation (a P2PKH spend gave 8). The block 170 test did
not catch it because that block's cost is far below the limit, which is exactly why the review
guide lists this spot among those without vector coverage.

## `CScript::GetSigOpCount(fAccurate)` — `getSigOpCount`

`GetOp` loop; failure *breaks* and returns the count so far; `CHECKSIG`/`CHECKSIGVERIFY` add 1;
`CHECKMULTISIG`/`VERIFY` add `DecodeOP_N(lastOpcode)` if accurate and `OP_1 ≤ lastOpcode ≤ OP_16`,
else 20; `lastOpcode` is the opcode just processed, and for a push it is the push opcode (at most
`OP_PUSHDATA4`, never in `OP_1..OP_16`). The Lean sets `last := 0` after a push and `last := c`
after an opcode, starting from `0xff` (`OP_INVALIDOPCODE`); the only reads of `last` are the range
test, so this is the same. Opcodes inside push data are never seen. Identical.

## `GetLegacySigOpCount` — `legacySigOpCount`

Inaccurate count over every `scriptSig` and every `scriptPubKey`. Identical.

## `GetP2SHSigOpCount` — `p2shSigOpCount` (after F1)

Coinbase → 0 (handled in `txSigOpCost`); for each input whose spent `scriptPubKey` is P2SH:
`GetSigOpCount(scriptSig)` = walk the scriptSig with `GetOp` keeping the last `vData` (cleared on
every call, so a trailing `OP_n` leaves it empty); parse failure or an opcode above `OP_16` → 0;
the accurate count of the subscript. The Lean `lastPush` and `getSigOpCount true` are this.
Identical.

## `CountWitnessSigOps`, `WitnessSigOps` — `countWitnessSigOps`, `witnessSigOps`

No `WITNESS` flag → 0; a witness-program output → `WitnessSigOps`; a P2SH output with a push-only
scriptSig whose last push is a witness program → `WitnessSigOps` of it; else 0. `WitnessSigOps`:
version 0 with a 20-byte program → 1; version 0 with a 32-byte program and a non-empty witness →
accurate count of the last witness element; anything else → 0. Identical.

## `GetTransactionSigOpCost` — `txSigOpCost`

`legacy × 4`; coinbase → that; `+ P2SH × 4` only with the `P2SH` flag; `+ Σ CountWitnessSigOps`
(which is 0 without `WITNESS`). Identical after F1.

## Vectors (`tests/SigOpVectors.lean`, 35 cases)

Expectations derived by hand from the rules above: accurate and inaccurate multisig counts with
`OP_3`, `OP_16`, `OP_1NEGATE`, `OP_NOP` and a push before `CHECKMULTISIG`; a truncated push ending
the count; opcodes inside push data; legacy counts over scriptSigs and outputs; the P2SH term for a
P2PKH spent output (0, the F1 case), a 2-of-3 redeem script (3), a trailing `OP_1` (0), a
non-push-only scriptSig (0), a malformed one (0); witness counts for P2WPKH, P2WSH, an empty
witness, version 1, a 25-byte program, P2SH-P2WPKH, P2SH-P2WSH, a non-push-only wrapper, a
non-program redeem script, and the `WITNESS` flag off; and transaction totals with and without each
flag, for a coinbase, and for the probe that exposed F1. All agree with the corrected definition.
