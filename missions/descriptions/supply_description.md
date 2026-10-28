## The claim

"There will only ever be 21 million bitcoin" is the most repeated statement about the system, and it is usually justified by the subsidy schedule alone: fifty coins, halved every 210,000 blocks, summing to just under 21 million. The schedule is proved in the subsidy mission (`BitcoinSubsidy.issuance_total`). But the schedule is a bound on what a coinbase *may* create; whether the chain's spendable supply stays within it depends on the whole validation path — that every non-coinbase transaction spends at least what it creates, that no input is spent twice, that the coinbase is bounded by the subsidy plus the fees actually collected, and that these checks run against the right ledger at every step. The inflation bug CVE-2018-17144 was a failure of exactly this composition, not of the schedule.

This mission states the bound as a property of every chain state reachable from the genesis under the block mission's `validate`, and proves it.

## What is proved

With `totalValue u` the sum of the values of the coins of a ledger and `issued n` the subsidy `GetBlockSubsidy` has issued to a chain of `n` blocks:

- **`update_bound`** — `UpdateCoins` raises the total by at most the value created and lowers it by the value spent (ledger arithmetic on a distinct-key ledger).
- **`values_in_range`** — every coin of a reachable state has a value in `[0, MAX_MONEY]`, because coins only enter as outputs that passed `CheckTransaction`.
- **`block_supply`** — one accepted block raises the total by at most `GetBlockSubsidy(height)`: the coinbase bound of `ConnectBlock` against the fees, through the acceptance theorem and `ApplySpec` of the block mission.
- **`supply_bound`** (goal) — on every reachable state, `totalValue S.utxo + genesisSubsidy ≤ issued S.nextHeight`.
- **`supply_lt_maxMoney`** — hence `totalValue S.utxo < MAX_MONEY` on every reachable state.

The genesis subsidy appears on the left because the source never adds the genesis coinbase to the UTXO set (`ConnectBlock`'s genesis shortcut), so it is issued but unspendable; the inequality is exact at the genesis state.

## What this rests on

The block mission's `acceptance` (the executable validation accepts iff the declarative specification holds), `apply_spec` (the resulting state is `ApplySpec`), `reachable_wellFormed` (distinct ledger keys), and the subsidy mission's `core_eq_spec` and `issuance_bound`. Nothing about the rules is re-transcribed here; the mission adds the quantities and the induction. ([`validation.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp), [`tx_verify.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp), [`coins.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp))
