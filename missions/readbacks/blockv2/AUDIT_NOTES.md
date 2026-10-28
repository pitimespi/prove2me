# Blind audit of the BitcoinBlockV2 revision

Read-backs in this directory were written by an independent sub-agent given only
`Definitions/Def_BitcoinBlockV2.lean`, the nineteen theorem stubs and the platform's
`mission_auditor.md`. They were produced while the user's Submit of the revision was
already compiling on the platform, so they are recorded here rather than attached to
the proposal items (published items take no read-back).

The auditor's closing concerns, with the disposition against Bitcoin Core
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`:

| # | Concern | Disposition |
|---|---------|-------------|
| 1 | `Def_BitcoinUtxo` imported but unused; `LedgerOk` unused. | Cosmetic; the block mission redefines the ledger with undo data. No effect on any statement. |
| 2 | `connectBlock` uses `coreSubsidy` and `setCompact`, the specs use `specSubsidy` and `specTarget`. | Intended: the specs are the declarative side; `BitcoinSubsidy.core_correct` and the PoW mission prove the pairs agree. |
| 3 | `TxsSpec` bounds fees from above only, while `connectLoop` requires `moneyRange`; `hpos`/`hfees` hypotheses. | Known (REVIEW_SPOT10.md): non-negativity of each fee follows from `checkTxInputs`; the side hypotheses state the invariant the proof needs. |
| 4 | `contextualCheck_iff` needs `hne`/`hvin` because of `headD` defaults. | Known; the hypotheses hold for every block that passed `checkBlock`. |
| 5 | `acceptance` assumes `Reachable S`. | Intended: the equivalence is stated for states reachable from genesis (`reachable_wellFormed`). |
| 6 | Genesis short-circuit in `connectBlock` and `LedgerSpec`. | Matches `ConnectBlock`'s `if (block.GetHash() == params.hashGenesisBlock)` early return. |
| 7 | `disconnect_connect`'s `hfresh` over all `o`, `hwf`/`hnd` roles. | Intended: freshness for every index is implied by the transaction's hash being new; the other hypotheses are used through `WellFormed`. |
| 8 | Coinbase scriptSig length checked on the head input only. | Equivalent: `isCoinBase` forces exactly one input, as the auditor notes. |
| 9 | Push resets `last` to 0; witness sigops unweighted; coinbase charged legacy sigops. | Matches Core: only `OP_1`..`OP_16` as `lastOpcode` matter, so 0 and a push opcode behave alike; `GetTransactionSigOpCost` adds witness sigops unweighted and is applied to every transaction including the coinbase (REVIEW_SPOT11.md, vectors in `tests/SigOpVectors.lean`). |
| 10 | Truncated `tipHeight − 2015`; literal index 227931 in `bip30Checked`. | Matches `GetAncestor` (clamped at genesis for short chains, mainnet only has retargets after height 2015) and `BIP34Height = 227931`. |
| 11 | `applyTxInUndo` looks up the ledger only when the undo height is 0; missing coins become `dummyCoin`. | Matches `ApplyTxInUndo` (`undo.nHeight == 0` means missing metadata, recovered via `AccessByTxid`); spot 18 of the review is still open. |
| 12 | `futureTime_iff` omits the version floor. | Intended: `ContextualCheckBlockHeader` tests the clock before the version. |
| 13 | `work_increases` reduces to `blockProof > 0`. | Intended: the statement is that an accepted block strictly increases chain work. |
| 14 | Dangling inputs read as value −1 at height 0; `mtpNat` clamps negatives. | Known (REVIEW_SPOT10.md): dangling inputs fail `checkTxInputs` before any value is used; MTPs are never negative on a chain whose genesis time is positive. |
