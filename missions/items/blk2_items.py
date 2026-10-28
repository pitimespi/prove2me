SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: AcceptBlockHeader, CheckBlockHeader, ContextualCheckBlockHeader, CheckBlock, CheckMerkleRoot, "
       "CheckWitnessMalleation, ContextualCheckBlock, ConnectBlock, GetBlockScriptFlags, IsBIP30Repeat, IsBIP30Unspendable, UpdateCoins, DisconnectBlock, ApplyTxInUndo, "
       "src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; "
       "CheckTransaction (consensus/tx_check.cpp); IsFinalTx, GetLegacySigOpCount, GetP2SHSigOpCount, GetTransactionSigOpCost, CheckTxInputs (consensus/tx_verify.cpp); "
       "CScript::GetSigOpCount, IsUnspendable (script/script.cpp, script.h); CountWitnessSigOps (script/interpreter.cpp); AddCoin, SpendCoin, AddCoins (coins.cpp); "
       "GetBlockProof (chain.cpp); GetWitnessCommitmentIndex, GetBlockWeight (consensus/validation.h); CMainParams (kernel/chainparams.cpp)")
TAGS = ["bitcoin", "consensus", "block-validation", "connectblock", "bip30", "bip34", "undo", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinBlock",
    "definition_title": "Block validation composed (revision 2): header path, CheckBlock, ContextualCheckBlock, ConnectBlock, DisconnectBlock, and the declarative specification",
    "natural_language_statement": r"""**Constants.** `MAX_BLOCK_WEIGHT` = 4,000,000, `MAX_BLOCK_SIGOPS_COST` = 80,000, `WITNESS_SCALE_FACTOR` = 4, `LOCKTIME_THRESHOLD` = 500,000,000, `SEQUENCE_FINAL` = 0xffffffff, `MINIMUM_WITNESS_COMMITMENT` = 38, `BIP34_IMPLIES_BIP30_LIMIT` = 1,983,702, `MAX_FUTURE_BLOCK_TIME` = 7200 s, `COINBASE_MATURITY` = 100, `MAX_MONEY`; the mainnet hashes `BIP34Hash`, the two `script_flag_exceptions`, the two `IsBIP30Repeat` blocks (91842, 91880) and the two `IsBIP30Unspendable` blocks (91722, 91812), in serialized byte order.

**Transactions.** `isCoinBase` (one input with a null prevout), `isUnspendable` (`OP_RETURN` first or over 10,000 bytes), `valueOut`, `checkTransaction` (`CheckTransaction`: non-empty inputs and outputs, witness-stripped size within the weight limit, each output and the running total in `MoneyRange`, no duplicate prevouts, coinbase script 2–100 bytes, no null prevout otherwise), `isFinalTx`.

**Signature operations.** `getSigOpCount accurate` is `CScript::GetSigOpCount(fAccurate)`; `p2shSigOpCount` is the redeem-script count; `witnessSigOps`/`countWitnessSigOps` are `CountWitnessSigOps`; `legacySigOpCount` and `txSigOpCost` are `GetLegacySigOpCount` and `GetTransactionSigOpCost` (legacy and P2SH counts weighted by 4, witness counts unweighted; P2SH only with the flag).

**Ledger.** `Coin` (output, height, coinbase flag); a `Ledger` is an association list; `getCoin`, `haveCoin`, `accessCoin`, `spendCoin`, `addCoin` (unspendable outputs are not stored; an existing entry is replaced), `updateCoins` (`UpdateCoins`), `txUndo` (the coins an input list spends), `Equiv` (same coins), `keysNodup`, `LedgerOk`.

**Per-transaction checks.** `checkTxInputs` (`Consensus::CheckTxInputs`, returning the fee), `sequenceLocksOk` (`SequenceLocks` through the BIP68 mission), `inputScriptsOk` (`CheckInputScripts` through the complete `VerifyScript` with the Taproot branch and the spent outputs), and `connectLoop`, the transaction loop of `ConnectBlock` in source order (inputs, fee range, BIP68, sigop budget, scripts, `UpdateCoins`), accumulating the ledger, fees, sigop cost and undo data.

**Chain state.** `ChainState` is the list of validated headers from the genesis and the ledger; `initialState`; tip, heights, `timesTo`/`mtpAt`/`mtp` (`GetMedianTimePast` through the Header mission), `requiredBits` (`GetNextWorkRequired` through the PoW mission with the period's first block), `blockProof`/`chainWork` (`GetBlockProof`, `nChainWork`), `hashValue`.

**The validation path.** `checkBlock` (`CheckBlock` with proof of work and merkle root through the Merkle mission), `heightScript`/`witnessCommitmentIndex`/`checkWitnessMalleation`/`contextualCheckBlock` (`ContextualCheckBlock`), `bip30Checked` (`fEnforceBIP30 || nHeight >= BIP34_IMPLIES_BIP30_LIMIT`), `bip30Ok`, `connectBlock` (`ConnectBlock` after `CheckBlock`: genesis shortcut, BIP30, flags from the Activation mission, the loop, the coinbase bound with `GetBlockSubsidy`), `acceptHeader` (`AcceptBlockHeader` on the tip, in source order), and `validate S B t : Outcome` — the source-linked outcome $C(S,B,t)$ with constructors `accept S' undo`, `invalid`, `futureTime` (`BLOCK_TIME_FUTURE`) and `missingPrev`. `accepts`, and `Reachable` (from the genesis state through accepted blocks).

**Disconnect.** `applyTxInUndo`, `restoreInputs`, `spendOutputs`, `disconnectTx`, `disconnectTxs`, `disconnectBlock` (`DisconnectBlock` with the clean flag and the two exception blocks).

**Specification.** `TxSpec`, `valueIn`, `feeOf`, `TxInputsSpec` (existing mature coins, value bounds, the BIP68 *specification* `satisfiesBIP68`, every input script), `TxsSpec` (transactions applied in order), `applyTxs`, `totalFees`, `applySpec` ($\mathrm{ApplySpec}(S,B)$), `HeaderSpec` (the PoW mission's `specTarget` form, parent, difficulty, median-time floor, clock ceiling, version floors), `BlockSpec`, `ContextSpec`, `LedgerSpec` (BIP30 where it applies, the sequence, the coinbase bound with `specSubsidy`), `Valid` ($V(S,B,t)$), `LedgerOk`, `WellFormed`.

**Revision 2.** Supersedes the first publication of this definition: `p2shSigOpCount` is now the per-input term of `GetP2SHSigOpCount` (zero unless the spent output is P2SH); the first version also added the accurate count of every non-P2SH spent script, overcounting a P2PKH spend as 8 instead of 4 (stricter than Core, never more lenient). Found by the source review in the repository's `REVIEW_SPOT11.md`; nothing else changed and every theorem statement is identical.

**Formalization Note.** `fJustCheck` is false and script checks are always performed (no assumed-valid shortcut); the chain is linear (a header not on the tip is `missingPrev`, the orphan case); flags, subsidy, difficulty, median time, merkle root and scripts are the published missions' functions. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinBlock.genesis_checkBlock": dict(title="The genesis block passes CheckBlock",
    nl=r"""`checkBlock genesisBlock = true`: the mainnet genesis block satisfies the proof of work, the merkle root (its single txid), the size and structure rules, `CheckTransaction` and the sigop bound. Proved by kernel evaluation of SHA-256d.""",
    ms=("CheckBlock on the genesis block", "Kernel evaluation of the 80-byte header hash and the coinbase txid.")),
"BitcoinBlock.acceptHeader_iff": dict(title="The header path is the Header mission's contextual check",
    nl=r"""`acceptHeader S h now = accept S []` iff the proof of work holds, `h.prevBlock` is the tip's hash, and the Header mission's `contextualCheck` holds with the chain's tip height, times, required bits and the clock.""",
    ms=("AcceptBlockHeader — the if-chain", "Case analysis on the six tests.")),
"BitcoinBlock.futureTime_iff": dict(title="BLOCK_TIME_FUTURE characterized",
    nl=r"""`validate S b now = futureTime` iff the proof of work holds, the parent is the tip, the bits are the required ones, the time exceeds the median time past, and $now + 7200 < time$.""",
    ms=("The time-too-new outcome", "The header tests before the clock test must pass; everything after is unreachable.")),
"BitcoinBlock.validate_clock": dict(title="The clock only matters through the future-time test",
    nl=r"""If `validate S b now ≠ futureTime` and $now \le now'$, then `validate S b now' = validate S b now`: an outcome that is not a time rejection is stable under later clock readings.""",
    ms=("Clock independence", "Only the one `if` reads the clock.")),
"BitcoinBlock.futureTime_transient": dict(title="A future-time rejection is transient",
    nl=r"""If `validate S b now = futureTime`, then for every $now' \ge time - 7200$ the outcome is not `futureTime`, and it equals the outcome at clock $time - 7200$: the block is not permanently invalidated by its time.""",
    ms=("Time-dependent rejection does not persist", "The futureTime characterization plus clock independence.")),
"BitcoinBlock.checkTransaction_iff": dict(title="CheckTransaction characterized",
    nl=r"""`checkTransaction tx = true` iff `TxSpec tx`: non-empty inputs and outputs, stripped size within the limit, every output value in $[0, \mathrm{MAX\_MONEY}]$ and the total at most `MAX_MONEY`, distinct prevouts, the coinbase script-length rule, and no null prevout for a non-coinbase.""",
    ms=("CheckTransaction — the output loop", "Running totals in range iff each value in range and the total in range.")),
"BitcoinBlock.checkBlock_iff": dict(title="CheckBlock characterized",
    nl=r"""`checkBlock b = true` iff the proof of work holds and `BlockSpec b`: non-empty, merkle root matching and unmutated, size limits, exactly the first transaction a coinbase, every transaction well formed, legacy sigops within 80,000.""",
    ms=("CheckBlock — conjunction", "Each Boolean conjunct to its predicate; the first transaction via `headD`.")),
"BitcoinBlock.contextualCheck_iff": dict(title="ContextualCheckBlock characterized",
    nl=r"""For a non-empty block whose transactions have inputs, `contextualCheckBlock S b = true` iff `ContextSpec S b`: every transaction final against the lock-time cutoff (median time past once CSV is active, else the block time), the BIP34 coinbase height prefix when active, the witness commitment rule, and the weight limit.""",
    ms=("ContextualCheckBlock — conjunction", "The BIP34 clause through the first transaction's first input.")),
"BitcoinBlock.bip30_history": dict(title="When the BIP30 scan is skipped",
    nl=r"""`bip30Checked S height hash = false` iff $height < 1{,}983{,}702$ and either the block is one of the two `IsBIP30Repeat` blocks or the chain has the BIP34 activation block (height 227,931) with hash `BIP34Hash` as an ancestor. On mainnet the scan is therefore skipped from height 227,932 to 1,983,701 except where BIP34 does not hold, and always performed from 1,983,702.""",
    ms=("fEnforceBIP30 and the BIP34 shortcut", "Boolean algebra on the two conditions.")),
"BitcoinBlock.checkTxInputs_iff": dict(title="CheckTxInputs characterized",
    nl=r"""`checkTxInputs u tx H` succeeds iff every input spends an existing coin with value in range that is mature if a coinbase ($height + 100 \le H$), the input total is in range, the outputs do not exceed it, and the fee is in range; the returned value is `valueIn − valueOut`.""",
    ms=("CheckTxInputs — the input loop", "Running totals and the `nSpendHeight - coin.nHeight` test with natural subtraction.")),
"BitcoinBlock.sequenceLocks_iff": dict(title="SequenceLocks is the BIP68 specification",
    nl=r"""`sequenceLocksOk u height mtp ltf tx = true` iff the BIP68 mission's `satisfiesBIP68` holds for the transaction's version, the lock-time flags, the context (height, median times) and the inputs' sequences and coin heights — with no admissibility hypothesis, through the published `fold_acceptance`.""",
    ms=("SequenceLocks through fold_acceptance", "`coreEnabled` is `specEnabled`; the initial accumulator evaluates true.")),
"BitcoinBlock.connectLoop_iff": dict(title="The ConnectBlock transaction loop characterized",
    nl=r"""For transactions with non-negative outputs and a non-negative fee total, the loop succeeds iff `TxsSpec`: each non-coinbase is admissible (`TxInputsSpec`) against the ledger left by its predecessors with the fee total within `MAX_MONEY`, and the accumulated sigop cost stays within 80,000, in order.""",
    ms=("The loop — induction", "`CheckTxInputs`, BIP68 and the script predicates, step by step.")),
"BitcoinBlock.connectBlock_iff": dict(title="ConnectBlock characterized",
    nl=r"""For a non-empty block with non-negative outputs, `connectBlock S b` succeeds iff `LedgerSpec S b`: the genesis shortcut, or the BIP30 freshness where the scan applies, the transaction sequence, and the coinbase value at most the fees plus the specification subsidy (`core_eq_spec`).""",
    ms=("ConnectBlock — BIP30, loop, coinbase bound", "The loop characterization and the subsidy equality.")),
"BitcoinBlock.connectBlock_apply": dict(title="ConnectBlock computes the declarative ledger",
    nl=r"""`connectBlock S b = some (u, undo)` implies `u = (applySpec S b).utxo`: the ledger after the source loop is the fold of `UpdateCoins` over the block's transactions (or unchanged for the genesis).""",
    ms=("The loop's ledger is the fold", "By `connectLoop_result`.")),
"BitcoinBlock.apply_spec": dict(title="Apply-spec equality",
    nl=r"""$C(S,B,t) = \mathrm{Accept}(S') \Longrightarrow S' = \mathrm{ApplySpec}(S,B)$: whenever the validation accepts, the resulting state is the declaratively specified one — the headers extended by the block's header and the ledger transformed by the block's transactions in order.""",
    ms=("ApplySpec", "The accept branch of `validate` and `connectBlock_apply`.")),
"BitcoinBlock.acceptance": dict(title="The acceptance theorem: C(S,B,t) accepts iff V(S,B,t)",
    nl=r"""For every chain state $S$ reachable from the genesis, candidate block $B$ and clock reading $t$:
$$R(S) \Longrightarrow \big(\exists S'\,u.\ \mathrm{validate}(S,B,t) = \mathrm{accept}(S',u) \iff \mathrm{Valid}(S,B,t)\big).$$
The source-linked validation path — `AcceptBlockHeader`, `CheckBlock`, `ContextualCheckBlock`, `ConnectBlock` with the published subsidy, difficulty, median-time, activation, merkle, script and BIP68 transcriptions — accepts exactly when the declarative specification admits the block: the header predicate (a valid compact target met by the hash, the tip as parent, the required difficulty, the median-time floor, the two-hour ceiling, the version floors), the block predicate, the contextual predicate, and the ledger predicate (BIP30 where it applies, every transaction admissible in sequence with the BIP68 specification and every input script verifying, the coinbase bounded by fees plus the specification subsidy).

**Formalization Note.** The reachability hypothesis is carried as in the goal contract; the equivalence holds for every state. Temporary future-time rejections are a separate outcome (`futureTime_iff`, `futureTime_transient`), and the resulting state is `ApplySpec` (`apply_spec`).""",
    ms=None),
"BitcoinBlock.reachable_wellFormed": dict(title="Reachable states are well formed",
    nl=r"""Every state reachable from the genesis has the genesis header first, pairwise distinct ledger keys, and only spendable coins created at heights between 1 and the tip.""",
    ms=("Invariants along accepted blocks", "`UpdateCoins` preserves distinct keys and adds coins at the new height.")),
"BitcoinBlock.work_increases": dict(title="Accepted blocks strictly increase the chain work",
    nl=r"""`validate S b now = accept S' undo` implies `S.chainWork < S'.chainWork`: `GetBlockProof` of a header with valid proof of work is at least one, so the most-work rule always prefers an extended chain.""",
    ms=("GetBlockProof is positive", "The derived target exists; the proof is `(~target / (target + 1)) + 1`.")),
"BitcoinBlock.disconnect_connect": dict(title="DisconnectBlock undoes ConnectBlock",
    nl=r"""For a well-formed state, a block with pairwise distinct txids whose outputs do not pre-exist (the BIP30 condition that BIP34 guarantees on mainnet) and that is not the genesis, if `validate S b now = accept S' undo` then `disconnectBlock S'.utxo height hash b undo = some (u, true)` for a ledger $u$ with exactly the coins of `S.utxo`: the undo data restores the previous ledger and the disconnect is clean.""",
    ms=("Connect then disconnect, transaction by transaction", "Outputs spent back cleanly, inputs restored in reverse with the recorded coins.")),
}
ORDER = ["BitcoinBlock.genesis_checkBlock","BitcoinBlock.acceptHeader_iff","BitcoinBlock.futureTime_iff","BitcoinBlock.validate_clock",
         "BitcoinBlock.futureTime_transient","BitcoinBlock.checkTransaction_iff","BitcoinBlock.checkBlock_iff","BitcoinBlock.contextualCheck_iff",
         "BitcoinBlock.bip30_history","BitcoinBlock.checkTxInputs_iff","BitcoinBlock.sequenceLocks_iff","BitcoinBlock.connectLoop_iff",
         "BitcoinBlock.connectBlock_iff","BitcoinBlock.connectBlock_apply","BitcoinBlock.apply_spec","BitcoinBlock.reachable_wellFormed",
         "BitcoinBlock.work_increases","BitcoinBlock.disconnect_connect","BitcoinBlock.acceptance"]
