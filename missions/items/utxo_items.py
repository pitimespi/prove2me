SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CheckTransaction, src/consensus/tx_check.cpp lines 11-68: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_check.cpp; "
       "Consensus::CheckTxInputs, src/consensus/tx_verify.cpp (lines 157-220): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp; "
       "CCoinsViewCache::AddCoin, AddCoins, SpendCoin, HaveInputs, src/coins.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/coins.cpp; "
       "UpdateCoins, BIP30 check (lines 2396-2475), fee accumulation and coinbase bound in Chainstate::ConnectBlock (lines 2518-2612), src/validation.cpp: "
       "https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; "
       "COIN, MAX_MONEY, MoneyRange, src/consensus/amount.h; COINBASE_MATURITY, src/consensus/consensus.h")
TAGS = ["bitcoin", "consensus", "utxo", "value-conservation", "formal-verification", "bitcoin-mainnet"]

DEFINITION = {
    "definition_name": "BitcoinUtxo",
    "definition_title": "UTXO set, transaction checks, and block value accounting",
    "natural_language_statement": r"""Amounts are integers in satoshi, $\mathrm{COIN} = 10^{8}$, $\mathrm{MAX\_MONEY} = 2.1 \times 10^{15}$, and $\mathrm{moneyRange}(v) \iff 0 \le v \le \mathrm{MAX\_MONEY}$; $\mathrm{COINBASE\_MATURITY} = 100$. Transaction ids form an arbitrary type $T$ with decidable equality.

**Data.** An outpoint is a pair (txid, index). An output carries a value and an `unspendable` bit, standing for `scriptPubKey.IsUnspendable()`. A coin is an output with its creation height and coinbase flag. A transaction has a txid, input outpoints, outputs, and a coinbase flag standing for `IsCoinBase()`. The UTXO set is a list of (outpoint, coin) entries; `keysNodup` says the outpoints are pairwise distinct.

**View operations.** `getCoin` looks up an outpoint; `haveCoin` tests presence; `spendCoin` removes the entry; `addCoin` does nothing for an unspendable output and otherwise inserts the entry in place of any entry with the same outpoint; `addCoinsFrom` adds outputs $i, i+1, \dots$ of a transaction; `spendInputs` spends a list of outpoints; `updateCoins` spends the inputs (unless coinbase) and adds the outputs, as `UpdateCoins`.

**Values.** `sumValues` sums output values; `valueOut` is `GetValueOut()`; `valueIn` sums the values of the coins at a list of outpoints (zero for a missing coin); `totalValue` sums the values held in the set.

**Checks.** `outputsLoop` is the output loop of `CheckTransaction`: each value non-negative and at most `MAX_MONEY`, the running total in range. `checkTransaction` requires non-empty inputs and outputs, the output loop, and pairwise distinct inputs. `haveInputs` is `HaveInputs`. `inputsLoop` is the input loop of `CheckTxInputs`: each input present, a coinbase coin mature (spend height minus coin height at least 100), each value and the running `nValueIn` in range. `checkTxInputs` then requires $\mathrm{nValueIn} \ge \mathrm{valueOut}$ and returns the fee $\mathrm{nValueIn} - \mathrm{valueOut}$ if in range.

**Blocks.** `bip30Ok` is the BIP30 pre-check: no output of any transaction of the block already exists in the view. `checkBlockTxs` requires the first transaction to be a coinbase, the others not, all passing `checkTransaction`. `connectLoop` processes the transactions in order: a non-coinbase must pass `checkTxInputs`, its fee is added to `nFees` which must stay in range, then `updateCoins`. `connectBlock`$_s$ runs the structural check, the BIP30 check, the loop, and the coinbase bound $\mathrm{valueOut}(\text{coinbase}) \le \mathrm{nFees} + s(\text{height})$ for a subsidy function $s$. `connectChain`$_s$ connects a list of blocks at consecutive heights. `subsidySum`$_s(h, n) = \sum_{i<n} s(h+i)$.

These definitions fix the value-accounting semantics of block connection for the conservation theorems.

**Formalization Note.** Heights are `Nat` and the maturity test uses truncated subtraction, which rejects a spend below the coin's height as the signed source does. `fEnforceBIP30` is fixed to enforced. Size, script-length, null-prevout and script-validity rules are not modeled. Only `Std` is imported.""",
}

THEOREMS = {
"BitcoinUtxo.checkTransaction_outputs": dict(title="CheckTransaction yields distinct inputs and in-range outputs",
    nl=r"""For every transaction $tx$ with $\mathrm{checkTransaction}(tx) = \mathtt{true}$: the input outpoints of $tx$ are pairwise distinct, and every output value $v$ of $tx$ satisfies $0 \le v \le \mathrm{MAX\_MONEY}$. These are the two facts of `CheckTransaction` that the value accounting consumes: the duplicate-input rejection (CVE-2018-17144) and the output-range loop (CVE-2010-5139).""",
    ms=("CheckTransaction — distinct inputs, in-range outputs", "Extract Nodup of inputs and per-output MoneyRange from the Boolean check.")),
"BitcoinUtxo.checkTxInputs_some": dict(title="CheckTxInputs returns the fee, in range, with all inputs present",
    nl=r"""For every view $U$, transaction $tx$, spend height $h$ and amount $f$ with $\mathrm{checkTxInputs}(U, tx, h) = \mathrm{some}(f)$:
$$f = \mathrm{valueIn}(U, tx.\mathrm{vin}) - \mathrm{valueOut}(tx), \qquad 0 \le f \le \mathrm{MAX\_MONEY},$$
and every input outpoint of $tx$ is present in $U$. The fee returned through `txfee` is exactly the difference of input and output values, and the input loop guarantees that every input it summed exists.""",
    ms=("CheckTxInputs — the fee identity", "Characterize a successful CheckTxInputs: fee = valueIn − valueOut, in MoneyRange, inputs present.")),
"BitcoinUtxo.totalValue_spend": dict(title="Spending a present coin removes exactly its value",
    nl=r"""For every view $U$ with pairwise distinct outpoints, outpoint $p$ and coin $c$ with $\mathrm{getCoin}(U, p) = \mathrm{some}(c)$,
$$\mathrm{totalValue}(\mathrm{spendCoin}(U, p)) = \mathrm{totalValue}(U) - c.\mathrm{value}.$$
Distinctness is what makes the removed entry unique.""",
    ms=("UTXO set — spending one coin", "Prove the total drops by the spent coin's value under keysNodup.")),
"BitcoinUtxo.totalValue_add_fresh": dict(title="Adding a coin at a fresh outpoint adds its value, or nothing if unspendable",
    nl=r"""For every view $U$, outpoint $p$ absent from $U$, and coin $c$,
$$\mathrm{totalValue}(\mathrm{addCoin}(U, p, c)) = \mathrm{totalValue}(U) + \begin{cases} 0 & c \text{ unspendable} \\ c.\mathrm{value} & \text{otherwise.}\end{cases}$$
This is `AddCoin` on a fresh outpoint: an `OP_RETURN`-style output is dropped, any other is stored.""",
    ms=("UTXO set — adding a fresh coin", "Prove the total rises by the value, or is unchanged for an unspendable output.")),
"BitcoinUtxo.totalValue_spendInputs": dict(title="Spending distinct present inputs removes exactly valueIn",
    nl=r"""For every view $U$ with pairwise distinct outpoints and list of outpoints $I$ that is itself duplicate-free and all of whose members are present in $U$,
$$\mathrm{totalValue}(\mathrm{spendInputs}(U, I)) = \mathrm{totalValue}(U) - \mathrm{valueIn}(U, I).$$
Without distinctness of $I$ the identity fails: a repeated outpoint is counted twice in `valueIn` but removed once.""",
    ms=("UTXO set — spending the inputs", "Prove the total drops by valueIn for Nodup, present inputs.")),
"BitcoinUtxo.tx_conservation": dict(title="An accepted ordinary transaction cannot create value",
    nl=r"""For every view $U$ with distinct outpoints, non-coinbase transaction $tx$ with distinct inputs, spend height $h$ and fee $f$ such that $\mathrm{checkTxInputs}(U, tx, h) = \mathrm{some}(f)$, provided no outpoint $(tx.\mathrm{txid}, j)$ with $j < |tx.\mathrm{vout}|$ is present in $U$ and every output value is non-negative,
$$\mathrm{totalValue}(\mathrm{updateCoins}(U, tx, h)) \le \mathrm{totalValue}(U) - f.$$
The ledger loses the fee, and loses more when an output is unspendable. The freshness hypothesis is the BIP30 condition; non-negativity of the outputs comes from `CheckTransaction`.""",
    ms=("Transaction — no value creation", "Combine the fee identity, spendInputs, and fresh additions to bound the ledger after an ordinary transaction.")),
"BitcoinUtxo.coinbase_bound": dict(title="A coinbase adds at most its output value",
    nl=r"""For every view $U$, coinbase transaction $tx$, height $h$, provided no outpoint $(tx.\mathrm{txid}, j)$ with $j < |tx.\mathrm{vout}|$ is present in $U$ and every output value is non-negative,
$$\mathrm{totalValue}(\mathrm{updateCoins}(U, tx, h)) \le \mathrm{totalValue}(U) + \mathrm{valueOut}(tx).$$
Equality holds when no output is unspendable.""",
    ms=("Coinbase — bounded by its outputs", "Bound the ledger after adding the coinbase outputs at fresh outpoints.")),
"BitcoinUtxo.block_bound": dict(title="An accepted block raises the ledger by at most the subsidy",
    nl=r"""For every subsidy function $s$, view $U$ with distinct outpoints, height $h$, and block $B$ whose transactions have pairwise distinct txids, if $\mathrm{connectBlock}_s(U, h, B) = \mathrm{some}(U', \mathrm{fees})$ then
$$\mathrm{totalValue}(U') \le \mathrm{totalValue}(U) + s(h),$$
and $U'$ has pairwise distinct outpoints. The fees paid by the block's transactions leave the ledger and are returned to it by the coinbase, which may add at most $s(h)$ beyond them.""",
    ms=("Block — at most the subsidy", "Thread conservation through the ConnectBlock loop with the BIP30 check and the coinbase bound.")),
"BitcoinUtxo.chain_bound": dict(title="A chain of accepted blocks raises the ledger by at most the summed subsidies",
    nl=r"""For every subsidy function $s$, list of blocks $B_1, \dots, B_n$ each with pairwise distinct txids, view $U$ with distinct outpoints and height $h$, if $\mathrm{connectChain}_s(U, h, [B_1, \dots, B_n]) = \mathrm{some}(U')$ then
$$\mathrm{totalValue}(U') \le \mathrm{totalValue}(U) + \sum_{i<n} s(h + i).$$""",
    ms=("Chain — summed subsidies", "Iterate the block bound over consecutive heights.")),
"BitcoinUtxo.ledger_bound": dict(title="From an empty ledger, total value never exceeds the subsidies issued",
    nl=r"""For every subsidy function $s : \mathbb N \to \mathbb Z$, starting height $h$, and sequence of blocks $B_1, \dots, B_n$ whose transactions have pairwise distinct txids within each block, if connecting them from the empty UTXO set succeeds,
$$\mathrm{connectChain}_s([\,], h, [B_1, \dots, B_n]) = \mathrm{some}(U) \;\Longrightarrow\; \mathrm{totalValue}(U) \le \sum_{i<n} s(h + i).$$
Here `connectChain` applies the transcribed `ConnectBlock` accounting — `CheckTransaction`, the BIP30 check, `CheckTxInputs`, fee accumulation, `UpdateCoins`, and the coinbase bound — at consecutive heights.

This is the supply bound of the ledger: fees move value between outputs, unspendable outputs destroy it, and the only creation is the coinbase, bounded by fees plus subsidy. With $s$ the mainnet `GetBlockSubsidy` and $h = 1$ (the genesis coinbase is never connected), the right-hand side is below $\mathrm{MAX\_MONEY}$ by the subsidy mission's bound.

**Formalization Note.** The subsidy is a parameter, so the statement does not depend on the schedule. Distinct txids within a block stand for collision-freedom of transaction hashes, which an abstract id type cannot supply; the BIP30 check is modeled as enforced.""",
    ms=None),
}
ORDER = ["BitcoinUtxo.checkTransaction_outputs","BitcoinUtxo.checkTxInputs_some","BitcoinUtxo.totalValue_spend",
         "BitcoinUtxo.totalValue_add_fresh","BitcoinUtxo.totalValue_spendInputs","BitcoinUtxo.tx_conservation",
         "BitcoinUtxo.coinbase_bound","BitcoinUtxo.block_bound","BitcoinUtxo.chain_bound","BitcoinUtxo.ledger_bound"]
