## Why value accounting matters

Bitcoin's ledger is a set of **unspent transaction outputs**: every coin that exists is an output of some transaction that no later transaction has spent. A transaction consumes outputs and creates new ones; the rule that it may not create value — that its outputs total at most its inputs — is what makes the supply finite, and the one exception, the **coinbase** transaction of each block, may create at most the block subsidy plus the fees the block's other transactions paid. Bitcoin Core enforces this through a handful of functions: `CheckTransaction` rejects negative or overflowing output values (CVE-2010-5139) and duplicate inputs (CVE-2018-17144); `CheckTxInputs` requires every input to be an existing, mature coin and computes the fee; `UpdateCoins` spends the inputs and adds the outputs; `ConnectBlock` accumulates the fees and rejects a coinbase that pays more than fees plus subsidy, after a BIP30 check that no output of the block already exists as an unspent coin. ([`tx_check.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp), [`tx_verify.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp), [`coins.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp), [`validation.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp))

Each of these checks has been the site of a real inflation bug. This mission transcribes them and proves the ledger-level consequence: starting from an empty ledger, after any sequence of accepted blocks the total value of all unspent outputs is at most the sum of the block subsidies.

## Coins, transactions, and the view

Amounts are integers in satoshi; `MoneyRange` is $0 \le v \le \mathrm{MAX\_MONEY} = 2.1 \times 10^{15}$. Transaction ids form an arbitrary type $T$ with decidable equality. An **outpoint** is a pair (txid, index). A **coin** is an output value together with its creation height, its coinbase flag, and whether its script is unspendable (the only script property the accounting reads: `AddCoin` never stores an unspendable output). A **transaction** has a txid, a list of input outpoints, a list of outputs, and a coinbase flag standing for `IsCoinBase()`. The **UTXO set** is a list of (outpoint, coin) entries with pairwise distinct outpoints; `getCoin` looks an outpoint up, `spendCoin` removes it, `addCoin` inserts (replacing any entry with the same outpoint, as `possible_overwrite` permits), and `totalValue` sums the stored values.

The transcribed rules: `checkTransaction` (non-empty inputs and outputs, the output-value loop with its running `MoneyRange` test, no duplicate inputs); `checkTxInputs` (all inputs present, coinbase inputs mature by `COINBASE_MATURITY` = 100, each input value and the running `nValueIn` in range, `nValueIn \ge` `GetValueOut()`, fee in range); `updateCoins` (spend inputs unless coinbase, add outputs); `bip30Ok`; `checkBlockTxs` (first transaction coinbase, others not, all passing `checkTransaction`); `connectLoop` (per-transaction fee accumulation with the running `MoneyRange` test, then `updateCoins`); `connectBlock` (the above, then `GetValueOut(coinbase) \le nFees + subsidy(height)`); and `connectChain`, which connects blocks at consecutive heights. The subsidy is a parameter $s : \mathbb N \to \mathbb Z$.

## Formalization targets

### Goal — the ledger never holds more than the subsidies issued
$$
\mathrm{connectChain}_s([\,],\ h_0,\ B_1 \cdots B_n) = \mathrm{some}(U) \;\Longrightarrow\; \mathrm{totalValue}(U) \le \sum_{i<n} s(h_0 + i),
$$
for every subsidy function $s$, starting height $h_0$, and sequence of blocks whose transactions have pairwise distinct txids within each block. This is `BitcoinUtxo.ledger_bound`. It is the weakest stable statement: the subsidy schedule is a parameter, so the result survives any change to it, and composing with the subsidy mission's bound gives the twenty-one-million cap as a corollary.

### Supporting milestones
1. **Output checks** (`checkTransaction_outputs`): an accepted transaction has distinct inputs and every output value in $[0, \mathrm{MAX\_MONEY}]$.
2. **The fee** (`checkTxInputs_some`): `CheckTxInputs` returns exactly $\mathrm{valueIn} - \mathrm{valueOut}$, in range, with every input present.
3. **Spending one coin** (`totalValue_spend`): removing a present coin lowers the total by exactly its value.
4. **Adding a fresh coin** (`totalValue_add_fresh`): adding at a fresh outpoint raises the total by the value, or by nothing if unspendable.
5. **Spending the inputs** (`totalValue_spendInputs`): spending distinct, present inputs lowers the total by $\mathrm{valueIn}$.
6. **Transaction conservation** (`tx_conservation`): an accepted ordinary transaction with fresh outputs lowers the ledger by at least its fee.
7. **Coinbase** (`coinbase_bound`): a coinbase with fresh outputs raises the ledger by at most its output value.
8. **Block** (`block_bound`): an accepted block raises the ledger by at most $s(h)$ and keeps outpoints distinct.
9. **Chain** (`chain_bound`): the same, summed over consecutive blocks, from any ledger.

## What the result establishes

The goal is a kernel-checked statement that the transcribed rules, applied from genesis, cannot put more value into the ledger than the subsidy schedule allows, for any transactions whatsoever: fees only move value, unspendable outputs only destroy it, and the coinbase is bounded by fees plus subsidy. The milestones give the exact per-transaction accounting the proof rests on, including the role of each historical fix: the `MoneyRange` loop (milestone 1), the duplicate-input rejection (milestones 5 and 6 need distinct inputs), and the BIP30 check (milestones 6 to 8 need fresh outputs).

Three hypotheses are the honest boundary of the result. Distinct txids within a block stand for the collision-freedom of transaction hashes, which an abstract id type cannot provide. The BIP30 check is modeled as enforced, which is true at every mainnet height except the two historical duplicate-coinbase blocks. And the genesis coinbase, which Bitcoin Core never connects to the UTXO set, is simply not among the blocks.

Status: every statement is open with an intentional placeholder proof. Nothing about compiled Bitcoin Core is claimed.

## Where the obvious argument fails

The naive argument — "inputs exceed outputs, so value cannot grow" — fails at three places that the actual code guards. Without distinct inputs, a transaction that lists the same outpoint twice would be credited its value twice while the view removes it once (CVE-2018-17144); the accounting lemma for spending needs `Nodup`. Without the BIP30 check, an output could overwrite an existing unspent coin and silently destroy or replace its value; the lemma for adding a coin needs the outpoint fresh, and freshness must be carried through the block from the initial view, which is where distinct txids enter. And the output values must be known non-negative before any sum is bounded, which is exactly what the `MoneyRange` loop supplies.

The fee is a second trap: `CheckTxInputs` computes it with signed arithmetic and tests it separately, so the proof must recover the identity $\text{fee} = \mathrm{valueIn} - \mathrm{valueOut}$ from the loop rather than assume it.

## Formalization scope

Amounts are `Int`; heights are `Nat`, and the maturity test uses truncated subtraction, which rejects a spend below the coin's height as the signed source does. The UTXO set is a keyed list; `keysNodup` is the map invariant and is proved preserved. Serialization-size, script-length, null-prevout and script-validity rules are not modeled; the coinbase flag is a field. The BIP30 enforcement flag, `fEnforceBIP30`, is fixed to its post-exception mainnet value.

A trivializing formalization would define `connectBlock` so that it fails whenever value would grow; every rule is transcribed from its source function. Restricting to blocks with no unspendable outputs or to transactions with a single input is out of scope.

No Mathlib is required; the development imports only `Std`. The composition with the subsidy mission's `BitcoinSubsidy.issuance_bound`, giving the absolute cap, is the intended follow-up theorem.

## Selected references

- Bitcoin Core contributors. *`CheckTransaction`*, `src/consensus/tx_check.cpp` at revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp)
- Bitcoin Core contributors. *`Consensus::CheckTxInputs`*, `src/consensus/tx_verify.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp)
- Bitcoin Core contributors. *`CCoinsViewCache::AddCoin`, `SpendCoin`, `HaveInputs`, `AddCoins`*, `src/coins.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp)
- Bitcoin Core contributors. *`UpdateCoins`, BIP30 check and fee accounting in `Chainstate::ConnectBlock`*, `src/validation.cpp`, same revision. [Source](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L2396)
- Pieter Wuille. *BIP30: Duplicate transactions*, 2012. [Specification](https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0030.mediawiki)
- Satoshi Nakamoto. *Bitcoin: A Peer-to-Peer Electronic Cash System*, 2008, sections 2 and 9. [Paper](https://bitcoin.org/bitcoin.pdf)
