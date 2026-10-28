SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockSubsidy, ConnectBlock (the coinbase bound), UpdateCoins, "
       "src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; "
       "CheckTxInputs (consensus/tx_verify.cpp); CheckTransaction (consensus/tx_check.cpp); AddCoin, SpendCoin (coins.cpp); MAX_MONEY (consensus/amount.h)")
TAGS = ["bitcoin", "consensus", "supply", "21-million", "utxo", "inflation", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinSupply",
    "definition_title": "The money supply of a chain state: the total value of the UTXO set, the issued subsidy, and the value-range invariant",
    "natural_language_statement": r"""Four names over the block mission's `BitcoinBlockV2` and the subsidy mission's `BitcoinSubsidy`; nothing is re-transcribed.

**`totalValue u`** — the sum of `nValue` over the coins of a ledger $u$ (an association list of outpoints and coins), as an integer.

**`ValuesInRange u`** — every coin of $u$ has `0 ≤ nValue ≤ MAX_MONEY` (the `MoneyRange` of `consensus/amount.h`).

**`issued n`** — `BitcoinSubsidy.issuedBelow n` as an integer: the sum of `GetBlockSubsidy` over heights $0, \dots, n-1$, i.e. the subsidy a chain of $n$ blocks has issued.

**`genesisSubsidy`** — `GetBlockSubsidy 0` as an integer, the fifty bitcoin of the genesis coinbase, which the source never adds to the UTXO set (`ConnectBlock`'s genesis shortcut; `CMainParams`).

**Formalization Note.** The chain state, the ledger, `updateCoins`, `validate` and `Reachable` are the block mission's; `coreSubsidy` and `issuedBelow` are the subsidy mission's. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinSupply.update_bound": dict(title="UpdateCoins creates at most the output value and destroys the input value",
    nl=r"""For a ledger $u$ with distinct keys and non-negative coin values, and a transaction with non-negative outputs, distinct prevouts, and (unless it is a coinbase) every input present in $u$: `totalValue (updateCoins u tx H) ≤ totalValue u + valueOut tx − (if coinbase then 0 else valueIn u tx.vin)`. The inequality (rather than equality) absorbs unspendable outputs, which `AddCoin` does not store, and overwritten coins.""",
    ms=("UpdateCoins — the ledger arithmetic", "`SpendCoin` removes exactly the coin at a key of a distinct-key ledger; `AddCoin` adds at most the new value.")),
"BitcoinSupply.values_in_range": dict(title="Every coin of a reachable state has a value in [0, MAX_MONEY]",
    nl=r"""For every chain state $S$ reachable from the genesis, `ValuesInRange S.utxo`: coins enter the ledger only as outputs of transactions that passed `CheckTransaction`, whose output loop enforces `MoneyRange` on each value.""",
    ms=("Coins come from checked outputs", "Membership in `applyTxs` is membership in the old ledger or in some transaction's outputs; `BlockSpec` gives `TxSpec` for every transaction.")),
"BitcoinSupply.block_supply": dict(title="An accepted block raises the UTXO total by at most its subsidy",
    nl=r"""For a reachable state $S$ and `validate S b now = accept S' undo`: `totalValue S'.utxo ≤ totalValue S.utxo + GetBlockSubsidy (S.nextHeight)`. The fees the coinbase collects were already in the ledger; only the subsidy is new value. Proved through the acceptance theorem and `ApplySpec`: the loop bound `totalValue (applyTxs) + totalFees ≤ totalValue + valueOut coinbase` and the coinbase bound `valueOut coinbase ≤ totalFees + subsidy`.""",
    ms=("The block loop bound", "Induction over the transactions with `update_bound`; the coinbase is the first transaction and the only one.")),
"BitcoinSupply.supply_bound": dict(title="The supply invariant: the UTXO total never exceeds the issued subsidy",
    nl=r"""For every chain state $S$ reachable from the genesis: `totalValue S.utxo + genesisSubsidy ≤ issued S.nextHeight`. The spendable supply plus the unspendable genesis subsidy is bounded by what `GetBlockSubsidy` has issued to the chain's height. No sequence of valid blocks creates value beyond the schedule: this is the invariant whose violation would be an inflation bug (CVE-2018-17144 broke it in Core by double-spending within a block; here duplicate inputs are rejected by `CheckTransaction` and the proof goes through the distinct-prevout condition).""",
    ms=None),
"BitcoinSupply.supply_lt_maxMoney": dict(title="The spendable supply is always below MAX_MONEY",
    nl=r"""For every reachable chain state $S$: `totalValue S.utxo < MAX_MONEY` (= 21,000,000 × 10^8 satoshi). From the supply invariant and the subsidy mission's `issuance_bound`.""",
    ms=("Below twenty-one million", "`issuedBelow n < MAX_MONEY` for every `n`, and the genesis subsidy is non-negative.")),
}
ORDER = ["BitcoinSupply.update_bound", "BitcoinSupply.values_in_range", "BitcoinSupply.block_supply",
         "BitcoinSupply.supply_bound", "BitcoinSupply.supply_lt_maxMoney"]
