# Read-back: `BitcoinBlock.connectLoop_iff`

## Binders and hypotheses

- $f$ : a record of seven Boolean script flags (p2sh, witness, taproot, dersig, cltv, csv, nulldummy).
- $H \in \mathbb{N}$ : the block height used for maturity, coin creation and BIP68.
- $\mathit{mtp} : \mathbb{N} \to \mathbb{N}$ : a median-time-past function by height (arbitrary).
- $\mathit{ltf} \in \mathbb{N}$ : the lock-time flags word.
- $\mathit{txs}$ : a list of serialized transactions.
- $u$ : a ledger (association list from outpoints to coins).
- $\mathit{fees} \in \mathbb{Z}$, $\mathit{sigOps} \in \mathbb{N}$ : initial accumulators.
- $\mathit{undo}$ : a block undo list (list of lists of coins), the initial undo accumulator.
- Hypothesis $h_{pos}$ : for every $tx \in \mathit{txs}$, $0 \le \mathrm{valueOut}(tx)$ (sum of its output values).
- Hypothesis $h_{fees}$ : $0 \le \mathit{fees}$.

The hypotheses and the binder $\mathit{undo}$ do not appear in the right-hand side of the conclusion.

## Conclusion

$$\big(\exists \mathit{st},\ \mathrm{connectLoop}(f, H, \mathit{mtp}, \mathit{ltf}, \langle u, \mathit{fees}, \mathit{sigOps}, \mathit{undo}\rangle, \mathit{txs}) = \mathrm{some}\,\mathit{st}\big) \iff \mathrm{TxsSpec}(f, H, \mathit{mtp}, \mathit{ltf}, u, \mathit{fees}, \mathit{sigOps}, \mathit{txs}).$$

### Left side, unfolded

$\mathrm{connectLoop}$ on the empty list returns $\mathrm{some}$ of the current state. On $tx :: \mathit{rest}$ from state $\langle v, F, \Sigma, U\rangle$:

1. **Fee/undo step.** If $\mathrm{isCoinBase}(tx)$ (exactly one input whose prevout is 32 zero bytes with index $2^{32}-1$): $(F, U)$ unchanged. Otherwise $\mathrm{checkTxInputs}(v, tx, H)$ must return $\mathrm{some}\,\mathit{fee}$ (every prevout present in $v$; for each input's coin $c$: not [coinbase and $H - c.\mathrm{height} < 100$ in natural subtraction], $c.\mathrm{out.nValue} \in [0,M]$, running sum in $[0,M]$; final $\mathit{valueIn} \ge \mathrm{valueOut}(tx)$; $\mathit{valueIn} - \mathrm{valueOut}(tx) \in [0,M]$; $\mathit{fee} = \mathit{valueIn} - \mathrm{valueOut}(tx)$; $M = 2.1\cdot10^{15}$), else fail; then $F + \mathit{fee} \in [0,M]$ else fail; then $\mathrm{sequenceLocksOk}(v, H, \mathit{mtp}, \mathit{ltf}, tx)$ else fail; new $F := F+\mathit{fee}$, $U := U \mathbin{+\!\!+} [\,[\mathrm{accessCoin}(v, i.\mathrm{prevout}) \mid i \in tx.\mathrm{vin}]\,]$.
2. $\Sigma' := \Sigma + \mathrm{txSigOpCost}(f, v, tx)$; fail if $\Sigma' > 80\,000$.
3. If not coinbase and $\mathrm{inputScriptsOk}(f, v, tx)$ is false, fail.
4. Continue on $\mathit{rest}$ from $\langle \mathrm{updateCoins}(v, tx, H), F', \Sigma', U'\rangle$.

Auxiliary meanings: $\mathrm{sequenceLocksOk}$ runs the BIP68 core calculation with version $tx.\mathrm{version} \bmod 2^{32}$, flags $\mathit{ltf} \bmod 2^{32}$, context $\langle H, \mathit{mtp}\rangle$ and inputs $\langle i.\mathrm{nSequence} \bmod 2^{32}, \mathrm{accessCoin}(v, i.\mathrm{prevout}).\mathrm{height}\rangle$ (height $0$ for a missing coin), returning whether the accumulated minimum height is $< H$ and the accumulated minimum time is $< \mathit{mtp}(H-1)$. $\mathrm{txSigOpCost}(f,v,tx) = 4\cdot\mathrm{legacySigOpCount}(tx) + $ (for non-coinbase) $4\cdot\sum_i \mathrm{p2shSigOpCount}$ if $f.\mathrm{p2sh}$, plus $\sum_i \mathrm{countWitnessSigOps}$, all against the spent scriptPubKeys from $\mathrm{accessCoin}$. $\mathrm{inputScriptsOk}(f,v,tx)$: for every index $n < |tx.\mathrm{vin}|$, the full `VerifyScript` (with the Taproot handler) succeeds for input $n$, with the spent-outputs list $[\mathrm{accessCoin}(v, j.\mathrm{prevout}).\mathrm{out} \mid j \in tx.\mathrm{vin}]$, context $\langle f, tx, n, \text{spent value}\rangle$, the input's scriptSig, the coin's scriptPubKey and the input's witness. $\mathrm{updateCoins}(v,tx,H)$: remove the entries keyed by $tx$'s prevouts (none for a coinbase), then add each spendable output $i$ as $\langle tx.\mathrm{vout}_i, H, \mathrm{isCoinBase}(tx)\rangle$ under $\langle\mathrm{txid}(tx), i\rangle$, replacing an existing entry.

### Right side, unfolded

$\mathrm{TxsSpec}(f,H,\mathit{mtp},\mathit{ltf},u,\mathit{fees},\mathit{sigOps},\mathit{txs})$: true for $[\,]$; for $tx :: \mathit{rest}$ from $(v, F, \Sigma)$:

- $\mathrm{isCoinBase}(tx) = \mathrm{false} \Rightarrow \big[\mathrm{TxInputsSpec}(f, v, H, \mathit{mtp}, \mathit{ltf}, tx) \wedge F + \mathrm{feeOf}(v,tx) \le M\big]$, where $\mathrm{feeOf}(v,tx) = \mathrm{valueIn}(v, tx.\mathrm{vin}) - \mathrm{valueOut}(tx)$ with $\mathrm{valueIn}$ summing $\mathrm{accessCoin}$ values (dummy $-1$ if missing), and $\mathrm{TxInputsSpec}$ is: $\forall i \in tx.\mathrm{vin}, \exists c, \mathrm{getCoin}(v, i.\mathrm{prevout}) = \mathrm{some}\,c \wedge (c.\mathrm{isCoinbase} = \mathrm{true} \Rightarrow c.\mathrm{height} + 100 \le H) \wedge 0 \le c.\mathrm{out.nValue} \le M$; $\mathrm{valueIn}(v, tx.\mathrm{vin}) \le M$; $\mathrm{valueOut}(tx) \le \mathrm{valueIn}(v,tx.\mathrm{vin})$; $\mathrm{satisfiesBIP68}$ (specification form: BIP68 not enabled, i.e. version $\bmod 2^{32} < 2$ or $\mathit{ltf} \bmod 2^{32}$ even, or every input is disabled (bit 31) or — time-based (bit 22): $\mathit{mtp}(c.\mathrm{height}-1) + 512\cdot(\text{seq} \bmod 2^{16}) \le \mathit{mtp}(H-1)$; height-based: $c.\mathrm{height} + (\text{seq} \bmod 2^{16}) \le H$ — with natural subtraction in $c.\mathrm{height}-1$ and $H-1$); and $\forall n < |tx.\mathrm{vin}|$, the same full script verification as in $\mathrm{inputScriptsOk}$ equals true;
- $\Sigma + \mathrm{txSigOpCost}(f, v, tx) \le 80\,000$;
- $\mathrm{TxsSpec}$ on $\mathit{rest}$ from $(\mathrm{updateCoins}(v,tx,H),\ F \text{ if coinbase else } F + \mathrm{feeOf}(v,tx),\ \Sigma + \mathrm{txSigOpCost}(f,v,tx))$.

Note that the right side imposes no lower bound on $F + \mathrm{feeOf}$ (the left requires $F+\mathit{fee} \ge 0$), which is where $h_{fees}$ and $h_{pos}$ enter.

## Edge cases silently included

Empty $\mathit{txs}$ (both sides trivially true); coinbase-shaped transactions anywhere in the list (no input checks either side); $\mathit{undo}$ arbitrary and irrelevant to the right side; $\mathit{mtp}$ arbitrary (e.g. non-monotone); 32-bit truncation of version, sequence and $\mathit{ltf}$; natural subtraction in maturity and in $\mathit{mtp}(\cdot - 1)$; missing coins give value $-1$ and height $0$ via $\mathrm{accessCoin}$ on both sides where it is used; duplicate keys in $u$ (first match wins).
