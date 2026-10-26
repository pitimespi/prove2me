# Read-back: `BitcoinBlock.connectBlock_apply`

## Binders and hypotheses

- $S$ : a chain state $\langle \mathit{headers}, \mathit{utxo}\rangle$.
- $b$ : a serialized block (header, transaction list $b.\mathrm{vtx}$).
- $u$ : a ledger (association list from outpoints to coins).
- $\mathit{undo}$ : a block undo list (a list of lists of coins).
- Hypothesis $h$ : $\mathrm{connectBlock}(S, b) = \mathrm{some}(u, \mathit{undo})$.

## Conclusion

$$u = \big(\mathrm{applySpec}(S,b)\big).\mathrm{utxo}.$$

### Hypothesis, unfolded

Let $\mathit{hash}$ be the double-SHA256 of the serialized header of $b$ and $\mathit{height} = |S.\mathrm{headers}|$. $\mathrm{connectBlock}(S,b)$ is:

1. if $\mathit{hash}$ equals the genesis hash constant: $\mathrm{some}(S.\mathrm{utxo}, [\,])$;
2. else if $\mathrm{bip30Checked}(S, \mathit{height}, \mathit{hash})$ (the block is not one of the two historical repeat blocks and the header at index $227931$ of $S$ is either absent or has a hash different from the BIP34 hash constant, or $\mathit{height} \ge 1983702$) and $\mathrm{bip30Ok}(S.\mathrm{utxo}, b)$ fails (some transaction $tx$ of $b$ and some index $o < |tx.\mathrm{vout}|$ have $\langle\mathrm{txid}(tx), o\rangle$ present in $S.\mathrm{utxo}$): none;
3. else run $\mathrm{connectLoop}$ with flags $= \mathrm{blockScriptFlags}(\mathit{height}, \mathrm{scriptException}(\mathit{hash}))$ (base flags P2SH/witness/taproot, or none for the BIP16 exception block, or P2SH/witness for the Taproot exception block; plus DERSIG, CLTV, CSV, NULLDUMMY when $\mathit{height}$ is at least $363725$, $388381$, $419328$, $481824$ respectively), the height, the median-time-past function $k \mapsto \max(0, \mathrm{mtpAt}(S,k))$, lock-time flags ($1$ if $\mathit{height} \ge 419328$ else $0$), starting state $\langle S.\mathrm{utxo}, 0, 0, [\,]\rangle$, over $b.\mathrm{vtx}$: if it returns none, none; otherwise with final state $\mathit{st}$, none if $\mathrm{valueOut}(\text{head of } b.\mathrm{vtx}, \text{default genesis coinbase}) > \mathit{st}.\mathrm{fees} + \mathrm{coreSubsidy}(\mathit{height})$, else $\mathrm{some}(\mathit{st}.\mathrm{utxo}, \mathit{st}.\mathrm{undo})$.

The loop processes transactions in order from state $\langle \mathit{utxo}, \mathit{fees}, \mathit{sigOps}, \mathit{undo}\rangle$: for a coinbase ($\mathrm{isCoinBase}$: exactly one input with null prevout) the fee and undo are unchanged; otherwise $\mathrm{checkTxInputs}$ on the current ledger must succeed with some fee, $\mathit{fees}+\mathit{fee}$ must be in $[0, 2.1\cdot10^{15}]$, BIP68 sequence locks must hold, and the undo gets the list of coins (via $\mathrm{accessCoin}$, dummy if missing) spent by the inputs appended; then $\mathit{sigOps}$ is increased by the transaction's sigop cost and must be $\le 80\,000$; then for a non-coinbase every input script must verify; then the ledger becomes $\mathrm{updateCoins}(\mathit{utxo}, tx, \mathit{height})$ and the loop continues.

### Conclusion, unfolded

$\mathrm{applySpec}(S,b).\mathrm{utxo}$ is $S.\mathrm{utxo}$ if $\mathit{hash}$ equals the genesis hash, and otherwise $\mathrm{applyTxs}(\mathit{height}, S.\mathrm{utxo}, b.\mathrm{vtx})$, the left fold of $\mathrm{updateCoins}(\cdot, tx, \mathit{height})$ over the transactions in order, where $\mathrm{updateCoins}(v, tx, H)$ removes from $v$ every entry keyed by a prevout of $tx$ (nothing removed for a coinbase) and then adds, for $i = 0,1,\dots$, the coin $\langle tx.\mathrm{vout}_i, H, \mathrm{isCoinBase}(tx)\rangle$ under key $\langle\mathrm{txid}(tx), i\rangle$ — skipping outputs whose scriptPubKey is unspendable (starts with byte $0x6a$, or is longer than $10\,000$ bytes), and otherwise prepending the new entry after removing any existing entry with that key.

So the statement says: whenever the executable connection succeeds with ledger $u$, that ledger equals the one obtained by folding $\mathrm{updateCoins}$ over the block's transactions (or $S.\mathrm{utxo}$ for the genesis-hashed shortcut). The $\mathit{undo}$ component is not constrained by the conclusion.

## Edge cases silently included

Genesis-hashed block (both sides give $S.\mathrm{utxo}$); empty $b.\mathrm{vtx}$ (loop returns the initial state, the coinbase bound is checked against the genesis coinbase's $50\cdot 10^8$ output, and $\mathrm{applyTxs}$ is the identity); a block whose transactions are not checked by $\mathrm{checkBlock}$ (e.g. a coinbase-shaped transaction in a later position is treated as a coinbase by the loop and by $\mathrm{updateCoins}$ alike); duplicate keys in $S.\mathrm{utxo}$; the hypothesis may be unsatisfiable, making the statement vacuous.
