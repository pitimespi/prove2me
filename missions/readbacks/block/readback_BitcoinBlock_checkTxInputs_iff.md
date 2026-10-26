# Read-back: `BitcoinBlock.checkTxInputs_iff`

## Binders

- $u$ : a ledger, i.e. a list of pairs $(\mathit{op}, c)$ where $\mathit{op}$ is an outpoint $\langle \text{hash bytes}, n\in\mathbb{N}\rangle$ and $c$ is a coin $\langle \mathrm{out}, \mathrm{height}, \mathrm{isCoinbase}\rangle$ with $\mathrm{out}$ an output (value $\in\mathbb{Z}$, scriptPubKey), $\mathrm{height}\in\mathbb{N}$, $\mathrm{isCoinbase}$ a Boolean. Keys need not be distinct.
- $tx$ : a serialized transaction (version, inputs $tx.\mathrm{vin}$, outputs $tx.\mathrm{vout}$, lock time).
- $H \in \mathbb{N}$ : the spend height.

There are no hypotheses.

## Conclusion

The conclusion is a conjunction of two parts.

**Part 1 (an equivalence):**
$$\big(\exists \mathit{fee},\ \mathrm{checkTxInputs}(u, tx, H) = \mathrm{some}\,\mathit{fee}\big) \iff \Big( \forall i \in tx.\mathrm{vin},\ \exists c,\ \mathrm{getCoin}(u, i.\mathrm{prevout}) = \mathrm{some}\,c \wedge (c.\mathrm{isCoinbase} = \mathrm{true} \Rightarrow c.\mathrm{height} + 100 \le H) \wedge 0 \le c.\mathrm{out.nValue} \wedge c.\mathrm{out.nValue} \le M \Big) \wedge \mathrm{valueIn}(u, tx.\mathrm{vin}) \le M \wedge \mathrm{valueOut}(tx) \le \mathrm{valueIn}(u, tx.\mathrm{vin}) \wedge \mathrm{valueIn}(u, tx.\mathrm{vin}) - \mathrm{valueOut}(tx) \le M,$$
with $M = 2\,100\,000\,000\,000\,000$ (`MAX_MONEY`) and $100$ = `COINBASE_MATURITY`.

**Part 2 (an implication, for all fees):**
$$\forall \mathit{fee},\ \mathrm{checkTxInputs}(u,tx,H) = \mathrm{some}\,\mathit{fee} \Rightarrow \mathit{fee} = \mathrm{feeOf}(u, tx).$$

### Definitions unfolded

- $\mathrm{getCoin}(u, \mathit{op})$: the coin of the **first** entry of $u$ whose key equals $\mathit{op}$, or none.
- $\mathrm{accessCoin}(u, \mathit{op})$: $\mathrm{getCoin}(u,\mathit{op})$ if present, else the dummy coin $\langle \langle -1, [\,]\rangle, 0, \mathrm{false}\rangle$ (value $-1$).
- $\mathrm{valueOut}(tx) = \sum_{o\in tx.\mathrm{vout}} o.\mathrm{nValue}$ over $\mathbb{Z}$.
- $\mathrm{valueIn}(u, \mathit{ins}) = \sum_{i \in \mathit{ins}} \mathrm{accessCoin}(u, i.\mathrm{prevout}).\mathrm{out.nValue}$ over $\mathbb{Z}$ (a missing coin contributes $-1$).
- $\mathrm{feeOf}(u,tx) = \mathrm{valueIn}(u, tx.\mathrm{vin}) - \mathrm{valueOut}(tx)$.
- $\mathrm{checkTxInputs}(u,tx,H)$: if some input's prevout has no coin in $u$, none; otherwise run the input loop over $tx.\mathrm{vin}$ with accumulator $0$: for each input, look up its coin (none $\Rightarrow$ fail); if the coin is a coinbase and $H - c.\mathrm{height} < 100$ (natural-number subtraction, so $0$ when $c.\mathrm{height} > H$) then fail; let $\mathit{acc}' = \mathit{acc} + c.\mathrm{out.nValue}$; if $c.\mathrm{out.nValue} \notin [0, M]$ or $\mathit{acc}' \notin [0,M]$ then fail; else continue with $\mathit{acc}'$. If the loop fails, none. Otherwise with $\mathit{valueIn}$ the final accumulator: none if $\mathit{valueIn} < \mathrm{valueOut}(tx)$; none if $\mathit{valueIn} - \mathrm{valueOut}(tx) \notin [0, M]$; else $\mathrm{some}(\mathit{valueIn} - \mathrm{valueOut}(tx))$.

So Part 1 says: the executable check succeeds exactly when every input's prevout is present in $u$ with a coin that is mature if coinbase ($c.\mathrm{height}+100 \le H$) and whose value lies in $[0,M]$, the total input value (as computed with the dummy default, which is irrelevant when all coins exist) is at most $M$, the outputs do not exceed the inputs, and the difference is at most $M$. Part 2 says any fee returned equals $\mathrm{valueIn} - \mathrm{valueOut}$.

## Edge cases silently included

Empty $tx.\mathrm{vin}$ (left: loop trivially succeeds with $\mathit{valueIn}=0$, so success iff $\mathrm{valueOut}(tx) \le 0$ and $-\mathrm{valueOut}(tx) \le M$; right: the universal clause is vacuous and the same three inequalities remain); negative output values are not excluded here, so $\mathrm{valueIn} - \mathrm{valueOut}$ can exceed $M$ (hence the last conjunct is not redundant); duplicate keys in $u$ (first match wins); coins with $c.\mathrm{height} > H$ (natural subtraction yields $0 < 100$, so a coinbase coin from the "future" fails, consistent with $c.\mathrm{height}+100 \le H$ failing); duplicate prevouts within $tx.\mathrm{vin}$ are not excluded and each is counted separately in $\mathrm{valueIn}$.
