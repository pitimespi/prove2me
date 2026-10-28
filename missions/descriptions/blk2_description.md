## Revision 2

This proposal supersedes the published mission *Bitcoin Block Validation Composed* (definition `BitcoinBlock`, 19 theorems). A line-by-line source review of that definition against the pinned revision found one transcription error: the transaction sigop cost added, for every non-P2SH spent output, the accurate sigop count of that output's script, whereas `GetP2SHSigOpCount` counts only redeem scripts of P2SH spent outputs. A plain P2PKH spend therefore cost 8 weight units instead of 4, so the model could reject a block Core accepts near the 80,000 limit, never the converse. The corrected `p2shSigOpCount` is the only change to the definition; all nineteen theorem statements are unchanged and their proofs re-check as they were. The review, the probe that exposed the error, and 35 sigop vectors with hand-derived expectations are in the repository (`REVIEW_SPOT11.md`, `tests/SigOpVectors.lean`).

## Why the composition is the consensus rule

Every component mission transcribed one layer of Bitcoin Core's validation: the subsidy schedule, compact targets and retargeting, the merkle root, the ledger accounting, median time past and the header rules, the activation heights and flag exceptions, serialization and hashing, the Script interpreter, the signature layer, the SegWit and Taproot dispatch. None of them is a consensus rule on its own. The rule is the way `AcceptBlockHeader`, `CheckBlock`, `ContextualCheckBlock` and `ConnectBlock` combine them — in which order the tests run, which ledger each transaction sees, where the fees and sigop costs accumulate, what the clock may reject, which historical blocks are exempt, and what state results. This mission writes that composition down, as the executable $C(S,B,t)$ of the umbrella contract, states the declarative $V(S,B,t)$ and $\mathrm{ApplySpec}(S,B)$ independently, and proves the two contract theorems. ([`validation.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp), [`tx_verify.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp), [`chainparams.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp))

## The validation path

A **chain state** is the list of validated headers from the genesis to the tip together with the UTXO set (a ledger of coins: output, creation height, coinbase flag). The genesis state holds the genesis header and an empty ledger, as the source never adds the genesis coinbase. A candidate block is offered with the local clock $t$; the outcome is `accept S' undo`, `invalid`, `futureTime` (`BLOCK_TIME_FUTURE`, a temporary rejection) or `missingPrev` (the block does not build on the tip).

**Header path** (`AcceptBlockHeader`): proof of work, the parent lookup, then `ContextualCheckBlockHeader` in source order — `nBits` against `GetNextWorkRequired` (the period's first block supplied from the chain), the median-time-past floor, the two-hour ceiling against the clock, the BIP34/66/65 version floors. **`CheckBlock`**: merkle root and mutation, size and count limits, exactly one coinbase first, `CheckTransaction` for every transaction, the legacy sigop bound. **`ContextualCheckBlock`**: `IsFinalTx` against the lock-time cutoff (median time past once CSV is active), the BIP34 height push in the coinbase, `CheckWitnessMalleation` (the commitment in the last qualifying coinbase output, the 32-byte nonce, or no witness at all), the weight limit. **`ConnectBlock`**: the genesis shortcut, the BIP30 scan with `IsBIP30Repeat` and the BIP34 shortcut, `GetBlockScriptFlags` with the two exception blocks, and the loop — `CheckTxInputs`, the fee range, `SequenceLocks`, `GetTransactionSigOpCost` against 80,000, `CheckInputScripts` through the complete `VerifyScript` (Taproot branch included), `UpdateCoins` — then the coinbase bound against `GetBlockSubsidy`. **`DisconnectBlock`** spends the block's outputs back and restores the inputs from the undo data in reverse, with the clean flag and the two unspendable-coinbase exceptions.

Every layer below is the published mission's function: `coreSubsidy`, `nextWorkRequired`, `checkProofOfWork`, `computeMerkleRoot`, `medianTimePast`, `versionOutdated`, `blockScriptFlags`, `lockTimeFlags`, `sequenceLocks`, `verifyScriptFull`. Nothing is re-transcribed.

## The specification

$V(S,B,t)$ is a predicate, not a program: a header predicate in the PoW mission's `specTarget` form with the parent, difficulty, time floor, clock ceiling and version floors; a block predicate; a contextual predicate; and a ledger predicate that quantifies over the transactions in sequence — each spends existing, mature coins of valid value, the inputs cover the outputs, the BIP68 *specification* `satisfiesBIP68` holds, every input script verifies, the fees and sigop costs stay within their bounds, BIP30 freshness holds where the scan applies, and the coinbase is bounded by the fees plus the *specification* subsidy. $\mathrm{ApplySpec}(S,B)$ extends the headers and folds `UpdateCoins` over the transactions.

## Formalization targets

1. **Genesis** (`genesis_checkBlock`): the mainnet genesis block passes `CheckBlock`, by kernel evaluation.
2. **Header path** (`acceptHeader_iff`), **time classification** (`futureTime_iff`, `validate_clock`, `futureTime_transient`): the future-time rejection is exactly characterized, transient, and the only clock dependence.
3. **Layer characterizations** (`checkTransaction_iff`, `checkBlock_iff`, `contextualCheck_iff`, `checkTxInputs_iff`, `sequenceLocks_iff`, `connectLoop_iff`, `connectBlock_iff`): each Boolean stage equals its predicate, the BIP68 one through the published `fold_acceptance`.
4. **History** (`bip30_history`): exactly when the BIP30 scan is skipped.
5. **State** (`connectBlock_apply`, `apply_spec`, `reachable_wellFormed`, `work_increases`): the resulting ledger is the fold, reachable states are well formed, chain work strictly increases.
6. **Undo** (`disconnect_connect`): the undo data restores the previous ledger, cleanly.
7. **Goal** (`acceptance`): $R(S) \Rightarrow (C(S,B,t)\text{ accepts} \iff V(S,B,t))$.

## What the result establishes

With the component missions, the umbrella's two contract theorems are now Lean theorems about a concrete, source-linked rendering of the pinned mainnet rules, with no parameter left abstract: hashes are SHA-256d, signatures are secp256k1 ECDSA and BIP340 Schnorr, scripts run through the full interpreter, and the historical exceptions are the source's. The definitions were exercised on the real chain: the genesis block, blocks 1–170 as the header chain, and block 170 — the first transaction between two users — validates end to end against the ledger holding block 9's coinbase, is rejected when its signature is altered or the spent coinbase is immature, is classified `futureTime` at an early clock, and disconnects back to the original ledger cleanly.

What remains outside: the proof-of-work hardness and signature unforgeability (computational assumptions, not functional correctness), the on-disk and networking layers, and a reorganization across multiple blocks, which is the disconnect theorem applied in sequence.

## Where the obvious argument fails

The loop breaks at the first failing transaction and threads four accumulators; its characterization needs the fee total and sigop cost to be non-negative so that running-range tests collapse to the final bound, which in turn needs the block predicate's non-negative outputs — the hypotheses on `connectLoop_iff` and `connectBlock_iff`. `CheckTxInputs` uses `nSpendHeight - coin.nHeight` with natural subtraction, which happens to agree with the specification form for every coin height. The future-time test sits in the middle of the header chain, so classifying it requires the four earlier tests to pass. `DisconnectBlock` restores inputs in reverse and spends outputs by exact match, so the identity needs the txids distinct, the outputs fresh and every ledger coin spendable with a positive height — which is where reachability and the BIP30 scan enter.

## Formalization scope

Policy is off; `fJustCheck` is false; assumed-valid shortcuts are not modeled (scripts are always checked). The chain is linear: a header whose parent is not the tip is the `missingPrev` outcome, as `BLOCK_MISSING_PREV` is not a validity verdict. Block hashes and byte orders are those of the serialization mission. No Mathlib is required; the development imports only `Std`.

## Selected references

- Bitcoin Core contributors. *`validation.cpp`*, *`consensus/tx_verify.cpp`*, *`consensus/tx_check.cpp`*, *`coins.cpp`*, *`kernel/chainparams.cpp`* at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp)
- Pieter Wuille. *BIP30: Duplicate transactions*, 2012. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0030.mediawiki)
- Gavin Andresen. *BIP34: Block v2, Height in Coinbase*, 2012. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0034.mediawiki)
- Thomas Kerin, Mark Friedenbach. *BIP113: Median time-past as endpoint for lock-time calculations*, 2015. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0113.mediawiki)
- Eric Lombrozo, Johnson Lau, Pieter Wuille. *BIP141: Segregated Witness*, 2015. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0141.mediawiki)
