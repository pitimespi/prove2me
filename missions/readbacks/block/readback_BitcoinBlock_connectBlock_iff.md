# Read-back: `BitcoinBlock.connectBlock_iff`

## Binders and hypotheses

- $S$ : a chain state $\langle \mathit{headers}, \mathit{utxo}\rangle$.
- $b$ : a serialized block (header and transaction list $b.\mathrm{vtx}$).
- Hypothesis $h_{ne}$ : $b.\mathrm{vtx} \ne [\,]$.
- Hypothesis $h_{pos}$ : for every transaction $tx$ in $b.\mathrm{vtx}$, $0 \le \mathrm{valueOut}(tx)$, where $\mathrm{valueOut}(tx) = \sum_{o \in tx.\mathrm{vout}} o.\mathrm{nValue}$ over $\mathbb{Z}$.

Both hypotheses are carried by the statement; neither appears in the conclusion.

## Conclusion

$$\big(\exists r,\ \mathrm{connectBlock}(S,b) = \mathrm{some}\,r\big) \iff \mathrm{LedgerSpec}(S,b).$$

### Left side, unfolded

With $\mathit{hash}$ the double-SHA256 of the serialized header of $b$ and $\mathit{height} = |S.\mathrm{headers}|$, $\mathrm{connectBlock}(S,b)$ returns some pair (ledger, undo) exactly in these cases:

- $\mathit{hash}$ equals the genesis hash constant (result $\mathrm{some}(S.\mathrm{utxo},[\,])$ unconditionally); or
- $\mathit{hash}$ is not the genesis hash, and **not** [$\mathrm{bip30Checked}(S,\mathit{height},\mathit{hash})$ and some output $\langle\mathrm{txid}(tx), o\rangle$, $tx \in b.\mathrm{vtx}$, $o < |tx.\mathrm{vout}|$, is present in $S.\mathrm{utxo}$], and the transaction loop $\mathrm{connectLoop}(\mathit{flags}, \mathit{height}, \mathrm{mtpNat}_S, \mathrm{ltf}, \langle S.\mathrm{utxo}, 0, 0, [\,]\rangle, b.\mathrm{vtx})$ returns some final state $\mathit{st}$, and $\mathrm{valueOut}(\mathrm{head}(b.\mathrm{vtx})) \le \mathit{st}.\mathrm{fees} + \mathrm{coreSubsidy}(\mathit{height})$.

Here $\mathrm{bip30Checked}$ is $(\neg\mathrm{isBIP30Repeat}(\mathit{height},\mathit{hash}) \wedge \neg\,\text{[header at index } 227931 \text{ exists and hashes to the BIP34 constant]}) \vee 1983702 \le \mathit{height}$; $\mathit{flags} = \mathrm{blockScriptFlags}(\mathit{height}, \mathrm{scriptException}(\mathit{hash}))$ (exception table keyed on two fixed hashes, then DERSIG/CLTV/CSV/NULLDUMMY by height thresholds $363725/388381/419328/481824$); $\mathrm{mtpNat}_S(k) = \max(0, \text{median of the first } 11 \text{ of the times of headers } 0..k \text{ most recent first})$; $\mathrm{ltf} = 1$ if $\mathit{height}\ge 419328$ else $0$; $\mathrm{coreSubsidy}(\mathit{height}) = 0$ if $\lfloor \mathit{height}/210000\rfloor \ge 64$, else $5\,000\,000\,000$ shifted right by $\lfloor\mathit{height}/210000\rfloor$ bits.

The loop, per transaction $tx$ from $\langle v, \mathit{fees}, \mathit{sigOps}, \mathit{undo}\rangle$: if $\mathrm{isCoinBase}(tx)$ the fee/undo step is trivial; else $\mathrm{checkTxInputs}(v, tx, \mathit{height})$ must be $\mathrm{some}\,\mathit{fee}$ (all prevouts present; coinbase coins mature: $\mathit{height} - c.\mathrm{height} \ge 100$ in natural subtraction; each coin value and running sum in $[0, M]$, $M = 2.1\cdot10^{15}$; inputs $\ge$ outputs; difference in $[0,M]$), $\mathit{fees}+\mathit{fee} \in [0,M]$, and $\mathrm{sequenceLocksOk}(v, \mathit{height}, \mathrm{mtpNat}_S, \mathrm{ltf}, tx)$ (the BIP68 core calculation on 32-bit truncations of the version, flags and sequences, with coin heights from $\mathrm{accessCoin}$, dummy height $0$ if missing); then $\mathit{sigOps} + \mathrm{txSigOpCost}(\mathit{flags}, v, tx) \le 80\,000$; then (non-coinbase) $\mathrm{inputScriptsOk}(\mathit{flags}, v, tx)$: for every input index $n$, the full script verification (legacy, P2SH, witness v0 and Taproot paths) of the input's scriptSig, the spent coin's scriptPubKey and the witness succeeds, in the context of $tx$, $n$, the spent amount and the list of all spent outputs; then continue with $\mathrm{updateCoins}(v, tx, \mathit{height})$.

### Right side, unfolded

$\mathrm{LedgerSpec}(S,b)$ is: $\mathit{hash} = \text{genesis hash}$, **or** the conjunction of

1. $\mathrm{bip30Checked}(S,\mathit{height},\mathit{hash}) = \mathrm{true} \Rightarrow \forall tx \in b.\mathrm{vtx},\ \forall o < |tx.\mathrm{vout}|,\ \mathrm{getCoin}(S.\mathrm{utxo}, \langle\mathrm{txid}(tx), o\rangle) = \mathrm{none}$;
2. $\mathrm{TxsSpec}(\mathit{flags}, \mathit{height}, \mathrm{mtpNat}_S, \mathrm{ltf}, S.\mathrm{utxo}, 0, 0, b.\mathrm{vtx})$: defined recursively — true for the empty list; for $tx :: \mathit{rest}$ from $(v, \mathit{fees}, \mathit{sigOps})$: [$\mathrm{isCoinBase}(tx) = \mathrm{false} \Rightarrow \mathrm{TxInputsSpec}(\mathit{flags}, v, \mathit{height}, \mathrm{mtpNat}_S, \mathrm{ltf}, tx) \wedge \mathit{fees} + \mathrm{feeOf}(v, tx) \le M$] $\wedge$ $\mathit{sigOps} + \mathrm{txSigOpCost}(\mathit{flags}, v, tx) \le 80\,000$ $\wedge$ $\mathrm{TxsSpec}$ on $\mathit{rest}$ from $(\mathrm{updateCoins}(v,tx,\mathit{height}),\ \mathit{fees} \text{ or } \mathit{fees}+\mathrm{feeOf}(v,tx) \text{ for non-coinbase},\ \mathit{sigOps}+\mathrm{txSigOpCost}(\mathit{flags},v,tx))$. $\mathrm{TxInputsSpec}$ requires: every input's prevout has a coin $c$ in $v$ with ($c$ coinbase $\Rightarrow c.\mathrm{height}+100 \le \mathit{height}$) and $0 \le c.\mathrm{out.nValue} \le M$; $\mathrm{valueIn}(v, tx.\mathrm{vin}) \le M$; $\mathrm{valueOut}(tx) \le \mathrm{valueIn}(v,tx.\mathrm{vin})$; the BIP68 specification predicate $\mathrm{satisfiesBIP68}$ on the same 32-bit truncated inputs (either BIP68 is not enabled — version below $2$ or flag bit $0$ clear — or every input is disabled (bit 31 set) or satisfies its height/time lock); and for every $n < |tx.\mathrm{vin}|$ the full script verification succeeds as in $\mathrm{inputScriptsOk}$;
3. for every $cb$ among the first one element of $b.\mathrm{vtx}$: $\mathrm{valueOut}(cb) \le \mathrm{totalFees}(\mathit{height}, S.\mathrm{utxo}, b.\mathrm{vtx}) + \mathrm{specSubsidy}(\mathit{height})$, where $\mathrm{totalFees}$ sums $\mathrm{feeOf}$ of each non-coinbase against the running ledger (coinbases contribute $0$) and $\mathrm{specSubsidy}(\mathit{height}) = \lfloor 5\,000\,000\,000 / 2^{\lfloor\mathit{height}/210000\rfloor}\rfloor$.

## Edge cases silently included

The hypotheses exclude an empty block and negative total outputs but nothing else (no $\mathrm{checkBlock}$: coinbase-shaped transactions in later positions, duplicate txids, missing coins defaulting to value $-1$ in $\mathrm{feeOf}$/$\mathrm{valueIn}$ on the right); genesis-hashed blocks satisfy both sides trivially; $\mathrm{coreSubsidy}$ versus $\mathrm{specSubsidy}$ (shift versus floor division, with a hard cut at $64$ halvings on the left); 32-bit truncation of version/sequence values in BIP68; $\mathrm{mtpNat}$ clamps negative medians to $0$; the undo component $r.2$ is unconstrained.
