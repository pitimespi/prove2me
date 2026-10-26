# Read-back: `BitcoinBlock.disconnect_connect`

## Binders and hypotheses

- $S$ : a chain state $\langle\mathit{headers}, \mathit{utxo}\rangle$.
- $b$ : a serialized block (header, transaction list $b.\mathrm{vtx}$).
- $\mathit{now} \in \mathbb{Z}$.
- $S'$ : a chain state.
- $\mathit{undo}$ : a block undo list (list of lists of coins).
- Hypothesis $h_{wf}$ : $\mathrm{WellFormed}(S)$: the first header of $S$ exists and is the genesis header; the keys (outpoints) of $S.\mathrm{utxo}$ are pairwise distinct; and every entry $(\mathit{op}, c)$ of $S.\mathrm{utxo}$ has $1 \le c.\mathrm{height} \le |S.\mathrm{headers}| - 1$ and $c.\mathrm{out.scriptPubKey}$ is not unspendable (does not start with byte $0x6a$ and is at most $10\,000$ bytes).
- Hypothesis $h_{nd}$ : the list $[\mathrm{txid}(tx) \mid tx \in b.\mathrm{vtx}]$ has no duplicates ($\mathrm{txid}$ = double-SHA256 of the witness-stripped serialization).
- Hypothesis $h_{fresh}$ : for every $tx \in b.\mathrm{vtx}$ and every $o \in \mathbb{N}$, $\mathrm{getCoin}(S.\mathrm{utxo}, \langle\mathrm{txid}(tx), o\rangle) = \mathrm{none}$ (no outpoint of any transaction of the block, at any index whatsoever, is a key of $S.\mathrm{utxo}$).
- Hypothesis $h_g$ : $\mathrm{headerHash}(b.\mathrm{header}) \ne \mathrm{genesisHash}$.
- Hypothesis $h$ : $\mathrm{validate}(S, b, \mathit{now}) = \mathrm{accept}(S', \mathit{undo})$.

## Conclusion

$$\exists u,\ \mathrm{disconnectBlock}\big(S'.\mathrm{utxo},\ |S.\mathrm{headers}|,\ \mathrm{headerHash}(b.\mathrm{header}),\ b,\ \mathit{undo}\big) = \mathrm{some}(u, \mathrm{true}) \;\wedge\; \mathrm{Equiv}(u, S.\mathrm{utxo}),$$
where $\mathrm{Equiv}(u,v)$ means $\forall \mathit{op},\ \mathrm{getCoin}(u,\mathit{op}) = \mathrm{getCoin}(v,\mathit{op})$ (first-match lookup agrees on every outpoint).

### Hypothesis $h$, unfolded

$\mathrm{validate}$ returns accept only when the header is accepted (PoW, parent $=$ tip hash, bits $=$ required bits, time $>$ tip median-time-past, time $\le \mathit{now}+7200$, version not outdated), $\mathrm{checkBlock}(b)$ holds, $\mathrm{contextualCheckBlock}(S,b)$ holds and $\mathrm{connectBlock}(S,b) = \mathrm{some}(u_1, \mathit{undo})$; then $S' = \langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], u_1\rangle$. Under $h_g$ the genesis shortcut of $\mathrm{connectBlock}$ is not taken, so $u_1$ and $\mathit{undo}$ come from the transaction loop at height $|S.\mathrm{headers}|$: $u_1$ is $S.\mathrm{utxo}$ with, for each transaction in order, the prevouts removed (non-coinbase only) and the spendable outputs added at that height with the coinbase flag; $\mathit{undo}$ has one entry per **non-coinbase** transaction, in order, each being the list of coins (from $\mathrm{accessCoin}$ on the running ledger) spent by its inputs.

### Conclusion, unfolded

$\mathrm{disconnectBlock}(v, H, \mathit{hash}, b, \mathit{undo})$: if $|\mathit{undo}| + 1 \ne |b.\mathrm{vtx}|$ then none; otherwise pair the transactions with $\mathrm{none} :: [\mathrm{some}\,c \mid c \in \mathit{undo}]$ (the first transaction gets no undo record, the $k$-th transaction gets the $(k-1)$-th undo entry), reverse the list, and process it with $\mathrm{disconnectTxs}(H, \mathit{exc}, v, \cdot)$ where $\mathit{exc} = \mathrm{isBIP30Unspendable}(H, \mathit{hash})$ (true only for the two fixed (height, hash) pairs $91722$ and $91812$). $\mathrm{disconnectTxs}$ handles the pairs in that (reversed) order, failing if any step fails and conjoining the clean flags. One step $\mathrm{disconnectTx}(v, H, \mathit{exc}, tx, \mathit{undo}_{tx})$: let $cb = \mathrm{isCoinBase}(tx)$; first $\mathrm{spendOutputs}$ walks $tx.\mathrm{vout}$ in forward order with index $i = 0,1,\dots$: an unspendable output is skipped (clean); otherwise the entry $\langle\mathrm{txid}(tx), i\rangle$ is removed from the ledger and the step is clean iff that outpoint was present with a coin equal to $\langle tx.\mathrm{vout}_i, H, cb\rangle$, or ($cb$ and $\mathit{exc}$). Then if $\mathit{undo}_{tx}$ is none the result is that ledger and flag; if it is $\mathrm{some}\,\mathit{coins}$: fail if $|\mathit{coins}| \ne |tx.\mathrm{vin}|$; else $\mathrm{restoreInputs}$ on the zipped (input, coin) list, which recurses on the tail first (so restores the last input first) and for each pair applies $\mathrm{applyTxInUndo}(\cdot, c, i.\mathrm{prevout})$: clean iff the prevout is currently absent; if $c.\mathrm{height} = 0$ then look for any entry of the ledger whose key hash equals the prevout hash — if found, take its height and coinbase flag for $c$, if not found **fail**; then add $c$ under the prevout (unspendable scripts are not added; otherwise the new entry replaces an existing one). The final flag is the conjunction of all step flags.

So the conclusion asserts that this disconnection of $b$ from $S'.\mathrm{utxo}$, with the height $|S.\mathrm{headers}|$ and the block's own header hash, succeeds, reports clean $=$ true, and yields a ledger that agrees with $S.\mathrm{utxo}$ on every lookup.

## Edge cases silently included

$h_{fresh}$ quantifies over all indices $o$, not only existing outputs; the conclusion needs the undo count to match, which under $h$ requires exactly one coinbase at the front (ensured by $\mathrm{checkBlock}$ inside $h$); $\mathrm{Equiv}$ compares first-match lookups only (ordering and duplicate shadowed entries are ignored); the $\mathit{exc}$ path ($\mathrm{isBIP30Unspendable}$) is reachable only at heights $91722$/$91812$ with the fixed hashes; $h$ may be unsatisfiable for some $S$, making the claim vacuous; $\mathit{now}$ is used only inside $h$; coins with height $0$ restored via the "find any entry with the same hash" fallback.
