# Read-back: `BitcoinBlockV2.checkTxInputs_iff`

**Binders.** $u$ is a ledger (a list of pairs (outpoint, coin), where a coin is an output, a natural-number height and a coinbase flag); $tx$ is a transaction; $H$ is a natural number (the spend height). No hypotheses.

**Conclusion.** A conjunction of two statements.

**(A)** The following are equivalent:

*Left:* there exists an integer $\mathit{fee}$ with $\mathrm{checkTxInputs}(u, tx, H) = \mathrm{some}(\mathit{fee})$. Unfolding: every input's prevout has a coin in $u$ (first-match lookup $\mathrm{getCoin}$); the input loop from accumulator $0$ succeeds — for each input in order, with its coin $c$: not (c is coinbase and $H \mathbin{\dot-} c.\mathit{height} < 100$, truncated subtraction), $c.\mathit{out}.\mathit{nValue} \in [0, \mathrm{MAX\_MONEY}]$ and the new running total $\in [0, \mathrm{MAX\_MONEY}]$ — yielding $V_{in}$; then $\lnot(V_{in} < \mathrm{valueOut}(tx))$ and $V_{in} - \mathrm{valueOut}(tx) \in [0, \mathrm{MAX\_MONEY}]$, returning $V_{in} - \mathrm{valueOut}(tx)$.

*Right:* the conjunction of
1. for every input $i$ of $tx$ there is a coin $c$ with $\mathrm{getCoin}(u, i.\mathit{prevout}) = \mathrm{some}(c)$, such that ($c.\mathit{isCoinbase} = \mathrm{true} \to c.\mathit{height} + 100 \le H$), $0 \le c.\mathit{out}.\mathit{nValue}$ and $c.\mathit{out}.\mathit{nValue} \le \mathrm{MAX\_MONEY}$;
2. $\mathrm{valueIn}(u, \mathit{vin}(tx)) \le \mathrm{MAX\_MONEY}$, where $\mathrm{valueIn}$ sums $\mathrm{accessCoin}(u, i.\mathit{prevout}).\mathit{out}.\mathit{nValue}$ over the inputs ($-1$ for a missing coin);
3. $\mathrm{valueOut}(tx) \le \mathrm{valueIn}(u, \mathit{vin}(tx))$, where $\mathrm{valueOut}$ is the integer sum of the output values;
4. $\mathrm{valueIn}(u, \mathit{vin}(tx)) - \mathrm{valueOut}(tx) \le \mathrm{MAX\_MONEY}$ (integer subtraction).

**(B)** For every integer $\mathit{fee}$, if $\mathrm{checkTxInputs}(u, tx, H) = \mathrm{some}(\mathit{fee})$ then $\mathit{fee} = \mathrm{feeOf}(u, tx) = \mathrm{valueIn}(u, \mathit{vin}(tx)) - \mathrm{valueOut}(tx)$.

Here $\mathrm{MAX\_MONEY} = 2\,100\,000\,000\,000\,000$ and $\mathrm{COINBASE\_MATURITY} = 100$.

**Edge cases silently included:** a transaction with no inputs (left: fee $= -\mathrm{valueOut}(tx)$ when that lies in $[0, \mathrm{MAX\_MONEY}]$; right: clause 1 vacuous, $\mathrm{valueIn} = 0$); negative output values (so $\mathrm{valueOut}$ may be negative and a "fee" may exceed the input sum); duplicate ledger keys (first match wins); the right side has no lower bound on $\mathrm{valueIn}$ other than that implied by clauses 1 and 3; the truncated subtraction $H \mathbin{\dot-} c.\mathit{height}$ on the left versus $c.\mathit{height} + 100 \le H$ on the right.
