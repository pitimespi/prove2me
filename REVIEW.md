# Human review guide: does the Lean model say what Bitcoin Core does?

Every theorem in this repository is kernel-checked. What is *not* checked by a machine is the one
step the whole result rests on: that each Lean definition in `Definitions/` computes what the
Bitcoin Core function it cites computes, at revision
[`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`](https://github.com/bitcoin/bitcoin/tree/a773e1e33b349dc819b5a0edc1c7a4839dc73b48)
with mainnet parameters. This document organizes that review.

## 1. Method

For each Lean declaration, three artifacts exist:

1. the Lean code (`Definitions/Def_*.lean`), whose docstring names the Core symbol;
2. the blind read-back (`missions/readbacks/<mission>/readback_Def_*.md`), written by an auditor
   who saw only the Lean code, describing in prose what it computes;
3. the Core source at the pinned revision (links below).

Review a declaration by reading the Core function first, writing down (or holding in mind) its
control flow, constants and edge behaviour, and then checking the read-back against that
expectation. Only then look at the Lean code, to resolve anything the read-back left ambiguous.
Reading the Lean first tends to make one read the intended meaning into it, which is the failure
mode the read-backs exist to prevent.

Five things to compare for every function:

- **Order of tests.** Where Core returns early, which test fires first matters for the theorems that
  characterize failure outcomes (`futureTime_iff`, `bip30_history`, the `_iff` theorems).
- **Constants and heights.** Every numeric literal in the Lean must match `consensus.h`,
  `chainparams.cpp`, `script.h`, `amount.h`.
- **Integer semantics.** Core uses `int`, `int64_t`, `uint32_t`, `CAmount`; the Lean uses `Nat`,
  `Int`, `BitVec`. Check every subtraction, every comparison of a signed with an unsigned value,
  every shift, and every place a value is reduced modulo 2^32 or 2^64.
- **Defaults and junk values.** Lean functions are total; `getD`, `headD`, `getLast?.getD`,
  `accessCoin`'s dummy coin and natural subtraction give values where Core would assert or be
  unreachable. Confirm those cases are unreachable in Core too, or excluded by a hypothesis.
- **Policy versus consensus.** Flags that are policy-only (`CLEANSTACK`, `MINIMALDATA`,
  `STRICTENC`, `LOW_S`, `NULLFAIL`, `DISCOURAGE_*`, `SIGPUSHONLY`, `CONST_SCRIPTCODE`) are off, as
  in `ConnectBlock`. Confirm nothing consensus-relevant was turned off with them.

The full list of declarations is `REVIEW_INDEX.md` (generated). The rest of this file points at the
places where a discrepancy is most likely to hide.

## 2. Known modeling limits (read these first)

These are deliberate and documented; the review should confirm they are the *only* deviations.

| # | Limit | Where | Consequence |
|---|---|---|---|
| L1 | **Legacy `OP_CODESEPARATOR` start position is not tracked.** In `SigVersion::BASE`, Core's `scriptCode` is the executed script *from the last executed `OP_CODESEPARATOR`*; the model uses the whole executed script (with `OP_CODESEPARATOR` instructions removed, as `SerializeScriptCode` does). | `Def_BitcoinVerify.evalBytes`, `Def_BitcoinSig.legacyOracle` | Exact for every script without an executed `OP_CODESEPARATOR`. A handful of historical mainnet transactions use it; for those the model's sighash differs from Core's. Tapscript tracks the position correctly. This is the one place where `verifyScriptFull` is known not to equal `VerifyScript`. |
| L2 | Fields are unbounded naturals. `nVersion`, `nTime`, `nBits`, `nNonce`, `nSequence`, `nLockTime` are `Nat`, reduced to 32 bits only where the Lean converts (`BitVec.ofNat 32`) or serializes. | `Def_BitcoinSer` structures, `Def_BitcoinBlockV2.isFinalTx`, `acceptHeader` | Values ≥ 2^32 cannot come from a parsed block (`readBlock` only produces bounded fields, `Block.wf`), but theorems quantify over all `Nat`. |
| L3 | The chain is linear: a header whose parent is not the tip is `missingPrev`; no block index, no fork tracking, no `FindMostWorkChain`. | `Def_BitcoinBlockV2.acceptHeader`, `validate` | Reorganization is `disconnect_connect` applied in sequence; it is not stated as one theorem. |
| L4 | No assumed-valid, no `fJustCheck`, no script cache, no `fChecked` short-circuit. Scripts are always verified. | `Def_BitcoinBlockV2.connectBlock` | Matches `-assumevalid=0`. |
| L5 | The genesis coinbase is not added to the UTXO set (as in Core); `initialState` has an empty ledger. | `Def_BitcoinBlockV2.initialState` | |
| L6 | `accessCoin` returns a dummy coin (value −1, height 0) for a missing outpoint where Core asserts. | `Def_BitcoinBlockV2.accessCoin`, `valueIn`, `txSigOpCost` | Reachable only after `CheckTxInputs` has established the coin exists; the `_iff` theorems carry that. |
| L7 | `ApplyTxInUndo`'s "missing metadata" branch (`undo.nHeight == 0`) restores from any ledger entry with the same txid, as `AccessByTxid` does; undo data produced by this model never has height 0. | `Def_BitcoinBlockV2.applyTxInUndo` | |
| L8 | Signet and testnet parameters, BIP94, `fPowAllowMinDifficultyBlocks` are not modeled (mainnet only). | `Def_BitcoinPow`, `Def_BitcoinBlockV2` | |
| L10 | **`OP_CHECKMULTISIG` deletes only the checked signature from the script code.** Core `FindAndDelete`s the pushes of all `nSigs` signatures before any check; the oracle interface sees one signature at a time. | `Def_BitcoinScript.multisigLoop`, `Def_BitcoinSig.checkSigPreTapscript` | Differs only when the executed script's own bytes contain a push of another signature of the same multisig (constructed cases in Core's `script_tests.json`; no standard template). Found in the spot 1 review, see `REVIEW_SPOT1.md`. |
| L9 | The BIP68 bridge in `ConnectBlock` uses the BIP68 mission's `Context.mtp : Nat → Nat`; the model takes `toNat` of the integer median time. | `Def_BitcoinBlockV2.ChainState.mtpNat` | Exact for non-negative times, i.e. every real chain. |

## 2b. Findings so far

| # | Finding | Status |
|---|---|---|
| F1 | `txSigOpCost` added the accurate sigop count of every non-P2SH spent output to a transaction's cost (Core's `GetP2SHSigOpCount` only counts P2SH redeem scripts); a P2PKH spend cost 8 instead of 4. The model was stricter than Core, never more lenient. | Fixed in `Definitions/Def_BitcoinBlockV2.lean` (`p2shSigOpCount`); all 19 proofs re-check; published on the platform as revision 2 (`BitcoinBlockV2`, all 19 proofs accepted), the original `BitcoinBlock` nodes deprecated with a note naming their replacements. See `REVIEW_SPOT11.md`. |
| L10 | multisig `FindAndDelete` (spot 1) | documented limit, not fixed (changes a published Script definition) |
| R1 | malformed script-code serialization (spot 2) | remark, cannot affect a verdict |
| R2 | `applyTxInUndo`'s legacy branch picks the sibling coin by ledger order, Core by lowest output index (spot 18) | remark, cannot affect a verdict; the branch is unreachable from the model's own undo data (L7) |
| D1, D2 | `blockProof` gives 0 for a target above `powLimit` where `GetBitsProof` would not; the negative flag read from the unshifted mantissa (spot 15) | remarks, cannot affect a verdict (such headers never enter a chain; the target is 0 in the other case) |

## 3. Risk-ranked review spots

**Status: all 23 spots reviewed** (reports `REVIEW_SPOT1.md` … `REVIEW_SPOT23.md`). One defect (F1, fixed, republished as `BitcoinBlockV2`), one documented limit found by the review (L10), four verdict-irrelevant remarks (R1, R2, D1, D2). Spots 15–17, 19, 20, 22, 23 were reviewed by independent sub-agents given the Lean files, the cached Core source and the blind read-backs; their vectors were re-run by the coordinator.

Ordered by how plausible a discrepancy is and how much depends on it. Links go to the pinned
revision; line numbers are where the function starts.

| Rank | Lean | Core | What to compare |
|---|---|---|---|
| 1 | `BitcoinScript.execOp`, `step`, `run` (`Def_BitcoinScript.lean`) — **reviewed, see `REVIEW_SPOT1.md`** | [`EvalScript`, interpreter.cpp:417](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L417) | The full opcode table: each opcode's stack effect, `CScriptNum` ranges (4 bytes in, 5 for CLTV/CSV), the operation count (only opcodes above `OP_16`, counted before execution, including skipped ones), `MAX_STACK_SIZE` checked after every op (also skipped ones), disabled opcodes failing even in unexecuted branches, `OP_CHECKMULTISIG` key/sig ordering and the `NULLDUMMY` test, `OP_IF` on an unexecuted branch, `OP_RETURN`/`OP_VERIFY`, `OP_CODESEPARATOR` (see L1). The Script audit found and fixed two gaps here once; it is where another would be. |
| 2 | `BitcoinSig.sigHashLegacy`, `scriptCodeBytes`, `findAndDelete` — **reviewed, see `REVIEW_SPOT2.md`** | [`SignatureHash`, interpreter.cpp:1610](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1610), [`FindAndDelete`:239](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L239) | `SIGHASH_SINGLE` with `nIn ≥ vout.size()` returning `uint256::ONE`; `ANYONECANPAY`; `NONE`/`SINGLE` blanking of other inputs' sequences; the hash type appended as 4 bytes; `FindAndDelete` matching only at instruction boundaries and deleting the *push* of the signature. Vectors: BIP143 example, generated spends. |
| 3 | `BitcoinSig.sigHashWitnessV0` — **reviewed in `REVIEW_SPOT2.md`** | same, `SigVersion::WITNESS_V0` branch | `hashPrevouts`/`hashSequence`/`hashOutputs` zeroing rules, the amount, `scriptCode` with its length prefix. |
| 4 | `BitcoinSig.parseDerLax`, `pubkeyVerify`, `parsePubkey` — **reviewed, see `REVIEW_SPOT4.md`** | [`ecdsa_signature_parse_der_lax`, pubkey.cpp:45](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp#L45), [`CPubKey::Verify`:283](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp#L283) | Lax parsing accepts what strict DER rejects (overlong lengths, leading zeros, >32-byte integers); S normalization; hybrid (`06`/`07`) keys accepted by `secp256k1_eckey_pubkey_parse`; `IsValid` (size only). Note `CheckPubKeyEncoding` with `STRICTENC` is policy. |
| 5 | `BitcoinSig.isValidSignatureEncoding`, `checkSignatureEncoding` — **reviewed, see `REVIEW_SPOT5.md`** | [interpreter.cpp:118](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L118), [:211](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L211) | Every one of the BIP66 byte tests; an empty signature passes the encoding check; the check applies only with `DERSIG` (`LOW_S`/`STRICTENC` are policy). |
| 6 | `BitcoinSig.ecdsaVerifyRaw`, `schnorrVerify`, field/group arithmetic — **reviewed, see `REVIEW_SPOT6.md`** | libsecp256k1 (semantics, not code) | The model implements the mathematics directly (affine arithmetic over the field); compare to the *specification* of ECDSA/BIP340 (r,s range checks, `R.x mod n = r`, even-y lifting, the BIP340 challenge tag), not to the constant-time code. Vectors: BIP340 test vectors, Python-signed ECDSA. |
| 7 | `BitcoinVerify.verifyScript`, `verifyWitnessProgram`, `executeWitnessScriptV0` — **reviewed, see `REVIEW_SPOT7.md`** | [`VerifyScript`:2012](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L2012), [`VerifyWitnessProgram`:1927](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1927), [`ExecuteWitnessScript`:1842](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1842) | The stack copy for P2SH, push-only test, the single-push rule for wrapped witness, "witness unexpected", unknown versions succeeding, pay-to-anchor, the 520-byte element test in `ExecuteWitnessScript`, `MAX_SCRIPT_SIZE` on the witness script. |
| 8 | `BitcoinTaproot.taprootHandler`, `executeTapscript`, `tapExecOp`, `evalChecksigTapscript` — **reviewed, see `REVIEW_SPOT8_9.md`** | [`VerifyWitnessProgram` v1 branch](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1927), [`EvalChecksigTapscript`:357](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L357) | Annex detection on the *raw* witness, control-block size arithmetic, leaf version mask, the validation weight starting at serialized-witness-size + 50, `OP_SUCCESSx` scan before anything else, `MINIMALIF`, `OP_CHECKSIGADD` stack order, unknown key types succeeding, `OP_CODESEPARATOR` position, no opcode count, 1000-element limit. Vectors: full BIP341 wallet test vectors. |
| 9 | `BitcoinTaproot.sigHashSchnorr`, `checkTapTweak`, `xonlyTweakAddCheck` — **reviewed, see `REVIEW_SPOT8_9.md`** | [`SignatureHashSchnorr`:1493](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L1493), [`CheckTapTweak`, pubkey.cpp:257](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pubkey.cpp#L257) | Every field of the BIP341 message in order, `spend_type`, the `SIGHASH_SINGLE` failure (no `ONE` quirk), the 65-byte signature with hash type 0 rejected, tweak < n, parity bit. |
| 10 | `BitcoinBlockV2.connectBlock`, `connectLoop` — **reviewed, see `REVIEW_SPOT10.md`** | [`ConnectBlock`, validation.cpp:2294](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2294) | Order inside the loop (`CheckTxInputs`, fee `MoneyRange`, `SequenceLocks`, sigop cost *for every tx including the coinbase*, scripts, `UpdateCoins`); `fEnforceBIP30` with `IsBIP30Repeat` and the BIP34 ancestor test, the 1,983,702 limit; the coinbase bound checked after the loop; `nLockTimeFlags`. |
| 11 | `BitcoinBlockV2.txSigOpCost`, `getSigOpCount`, `p2shSigOpCount`, `countWitnessSigOps` — **reviewed, defect F1 found and fixed, see `REVIEW_SPOT11.md`** | [`GetTransactionSigOpCost`, tx_verify.cpp:149](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L149), [`CScript::GetSigOpCount`, script.cpp:159](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.cpp#L159), [`CountWitnessSigOps`, interpreter.cpp:2149](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp#L2149) | Legacy counting stops at a parse failure (keeps the count so far); `lastOpcode` for the accurate multisig count; P2SH count uses the *last* push of the scriptSig and returns 0 if not push-only; witness count for P2WSH uses the last witness element; the ×4 weighting. |
| 12 | `BitcoinBlockV2.checkBlock`, `checkWitnessMalleation`, `witnessCommitmentIndex` — **reviewed, no defect, see `REVIEW_SPOT12.md`** | [`CheckBlock`:3926](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L3926), [`CheckWitnessMalleation`:3878](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L3878) | Merkle mutation; `vtx.size()*4` and serialized-size limits; the *last* qualifying output is the commitment; nonce exactly 32 bytes; the committed hash at bytes 6..38; when no commitment is expected, no transaction may have a witness. |
| 13 | `BitcoinBlockV2.contextualCheckBlock`, `heightScript`, `isFinalTx` — **reviewed, no defect, see `REVIEW_SPOT13.md`** | [`ContextualCheckBlock`:4137](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L4137), [`IsFinalTx`, tx_verify.cpp:23](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L23) | Cutoff = MTP once CSV is active for the *next* block, else the block time; BIP34 uses `CScript() << nHeight` (CScriptNum push) as a *prefix*; `IsFinalTx` compares `nLockTime` with the threshold 500,000,000; weight after the witness check. |
| 14 | `BitcoinBlockV2.acceptHeader`, `ChainState.requiredBits`, `mtp` — **reviewed, no defect, see `REVIEW_SPOT14.md`** | [`ContextualCheckBlockHeader`:4088](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L4088), [`GetNextWorkRequired`, pow.cpp:14](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L14) | Test order (bits, time-too-old, time-too-new, versions); the retarget's first block is the ancestor at `height − 2015`; MTP over the 11 most recent times with the median at index `size/2` of the sorted window. |
| 15 | `BitcoinPow.setCompact`, `getCompact`, `calculateNextWork` — **reviewed, no defect (two verdict-irrelevant differences D1/D2 recorded), see `REVIEW_SPOT15.md`** | [`arith_uint256::SetCompact`:176](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp#L176), [`GetCompact`:196](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp#L196), [`CalculateNextWorkRequired`, pow.cpp:50](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp#L50) | Negative/overflow flags, the 0x7fffff mask, `GetCompact` rounding when bit 23 is set; the timespan clamp; the 256-bit *modular* multiplication; `bnNew > powLimit` cap. |
| 16 | `BitcoinSer.readTx`, `serTx`, `readCompactSize`, `blockWeight` — **reviewed, no defect, see `REVIEW_SPOT16.md`** | `serialize.h`, `primitives/transaction.h`, `consensus/validation.h` | The witness marker `00 01` and the 0-input ambiguity in `UnserializeTransaction`; a tx with witnesses but all empty serializes *without* the flag; CompactSize canonical-encoding rejection and `MAX_SIZE`; `GetSerializeSize(TX_NO_WITNESS)` vs with witness for weight. |
| 17 | `BitcoinSer.sha256`, `ripemd160` — **reviewed, no defect; constants and tables compared programmatically, see `REVIEW_SPOT17.md`** | `crypto/sha256.cpp`, `crypto/ripemd160.cpp` | Checked by test vectors; a review need only confirm padding and endianness conventions. |
| 18 | `BitcoinBlockV2.disconnectBlock`, `applyTxInUndo`, `spendOutputs` — **reviewed, no defect (remark R2, unreachable legacy-undo branch), see `REVIEW_SPOT18.md`** | [`DisconnectBlock`:2178](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2178), [`ApplyTxInUndo`:2148](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2148) | Reverse order of transactions and of inputs; the "unspendable" skip; the exact-match test lowering `fClean`; the two `IsBIP30Unspendable` blocks; `DISCONNECT_FAILED` cases. |
| 19 | `BitcoinActivation.blockScriptFlags`, `scriptException`, `lockTimeFlags` — **reviewed, no defect; Taproot always-on is exactly Core's rule at this revision, see `REVIEW_SPOT19.md`** | [`GetBlockScriptFlags`:2249](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2249), [`CMainParams`, chainparams.cpp:108](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp#L108) | The two exception hashes and their flag sets; `DeploymentActiveAt` (height ≥) vs `DeploymentActiveAfter` (height + 1 ≥); heights 227931/363725/388381/419328/481824; Taproot is always on except the one block. |
| 20 | `BitcoinBIP68.coreStep`, `evaluate` — **reviewed, no defect, see `REVIEW_SPOT20.md`** | [`CalculateSequenceLocks`, tx_verify.cpp:45](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45) | Mask and shift constants; the `−1` offsets; `max(nCoinHeight − 1, 0)`; the `prevHeights[i] = 0` for disabled inputs; `EvaluateSequenceLocks` uses the *previous* block's MTP. |
| 21 | `BitcoinBlockV2.checkTransaction`, `checkTxInputs` — **reviewed, no defect, see `REVIEW_SPOT21.md`** | [`CheckTransaction`, tx_check.cpp:19](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp#L19), [`CheckTxInputs`, tx_verify.cpp:170](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L170) | Coinbase scriptSig 2–100; duplicate-input test via a set; maturity `nSpendHeight − nHeight < 100`; `MoneyRange` on each coin and the running total; fee range. |
| 22 | `BitcoinMerkle.computeMerkleRoot` — **reviewed, no defect, see `REVIEW_SPOT22.md`** | [`ComputeMerkleRoot`, merkle.cpp:51](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51) | Duplicate-last-element padding; mutation detected only for adjacent equal pairs at even positions; empty list gives the zero hash. |
| 23 | `BitcoinSubsidy.coreSubsidy` — **reviewed, no defect, see `REVIEW_SPOT23.md`** | [`GetBlockSubsidy`, validation.cpp:1833](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833) | The `halvings >= 64` early return; the right shift. |

## 4. What the vectors already cover

Running these reproduces the independent checks (each takes seconds to a few minutes):

```
cd <workspace with lake>; lake env lean tests/SerVectors.lean      # SHA-256/RIPEMD-160 vectors, genesis hash and merkle root
lake env lean tests/ScriptVectors.lean   # interpreter sanity cases
lake env lean tests/SigVectors.lean      # BIP340 vectors, BIP143 example, generated ECDSA/Schnorr spends
lake env lean tests/SighashVectors.lean  # 24 sighashes from an independent Python reference, SINGLE bug, FindAndDelete boundaries
lake env lean tests/LaxDerVectors.lean   # 29 lax-DER, S-normalization and key-encoding cases from a Python signer
lake env lean tests/DerEncodingVectors.lean # 30 BIP66 encoding and flag cases
lake env lean tests/VerifyVectors.lean   # 58 VerifyScript dispatch cases, signed P2WPKH / P2SH-P2WPKH / P2SH spends
lake env lean tests/TaprootVectors.lean  # the complete BIP341 wallet-test-vectors.json
lake env lean tests/TapscriptVectors.lean # 65 Python-signed Taproot spends: key path, script path, CHECKSIGADD, MINIMALIF, OP_SUCCESS, budget, CODESEPARATOR
lake env lean tests/SigOpVectors.lean    # 35 sigop-accounting cases with hand-derived expectations (includes the F1 probe)
lake env lean tests/SerEdgeVectors.lean     # 189 CompactSize / witness-marker / weight edge cases, from tests/reference/ser_reference.py
lake env lean tests/HashVectors.lean        # 86 SHA-256 / RIPEMD-160 / SHA-1 vectors incl. the million-'a' message, from tests/reference/hash_reference.py
lake env lean tests/TxCheckVectors.lean     # 35 CheckTransaction / CheckTxInputs boundary cases, from tests/reference/txcheck_undo_reference.py
lake env lean tests/UndoVectors.lean        # 32 DisconnectBlock / ApplyTxInUndo cases incl. the BIP30 exceptions, from tests/reference/txcheck_undo_reference.py
lake env lean tests/PowVectors.lean         # 205 SetCompact/GetCompact/retarget/CheckProofOfWork cases incl. the real retargets at 2016 and 32256, from tests/reference/pow_reference.py
lake env lean tests/ActivationVectors.lean  # 114 script-flag / activation-height / exception-block cases, from tests/reference/activation_reference.py
lake env lean tests/Bip68Vectors.lean       # 136 CalculateSequenceLocks / EvaluateSequenceLocks cases, from tests/reference/bip68_reference.py
lake env lean tests/MerkleVectors.lean      # 36 ComputeMerkleRoot mutation cases (string combine and real SHA-256d), from tests/reference/merkle_reference.py
lake env lean tests/SubsidyVectors.lean     # 93 GetBlockSubsidy boundary cases and the issuance total, from tests/reference/subsidy_reference.py
lake env lean tests/HeaderPathVectors.lean  # 43 header-path outcome-order, retarget-ancestor, MTP and version-floor cases (real block 170 header)
lake env lean tests/ContextualVectors.lean  # 57 ContextualCheckBlock / IsFinalTx / height-push cases, from tests/reference/contextual_reference.py
lake env lean tests/CheckBlockVectors.lean  # 47 CheckBlock / merkle mutation / witness commitment cases (block 586 + synthetic), from tests/reference/checkblock_reference.py
lake env lean tests/Block170Test.lean    # mainnet headers 0–170 and block 170 end to end, tampered variants, disconnect
```

A vector exercises one path; it does not replace reading the branches it does not reach (error
paths, limits, historical exceptions). The spots above with no vector coverage are 10 (BIP30 and
the BIP34 ancestor test), 12 (witness commitment), 13 (BIP34 height prefix), 18 (disconnect
failure cases) and 19 (the exception blocks): review those by reading. Spot 11 now has vectors;
its defect F1 was found by reading, which is the point.

## 5. Checklist

Tick each line when the Core function, the read-back and the Lean agree, noting any discrepancy
with the Lean name, the Core line, the input that distinguishes them, and whether a theorem
statement or only a definition is affected.

- [ ] Section 2 limits L1–L10 are the only deviations found.
- [ ] Spots 1–23 reviewed against the linked source.
- [ ] Every row of `REVIEW_INDEX.md` has been assigned to a spot above or confirmed as a pure helper.
- [ ] Constants: `consensus.h`, `script.h` (`MAX_SCRIPT_SIZE`, `MAX_STACK_SIZE`, `MAX_OPS_PER_SCRIPT`, `MAX_PUBKEYS_PER_MULTISIG`, `MAX_SCRIPT_ELEMENT_SIZE`, `LOCKTIME_THRESHOLD`), `amount.h` (`MAX_MONEY`), `chainparams.cpp` (heights, hashes), `interpreter.h` (`VALIDATION_WEIGHT_*`, `TAPROOT_*`, `ANNEX_TAG`).
- [ ] Byte orders: block hashes are compared in serialized (little-endian) order everywhere; the exception and BIP34 hashes in `Def_BitcoinBlockV2` and the genesis hash in `Def_BitcoinSer` are display hex reversed.
- [ ] Each vector file runs and prints only `true`/expected values.

If a discrepancy is found, the fix is a definition change followed by re-running `tools/pipeline.py`
(stubs, split, stage, a fresh blind audit) and resubmitting the affected proofs; theorem statements
whose meaning changes need a new proposal revision.
