# Read-back: `BitcoinBlock.contextualCheck_iff`

## Binders and hypotheses

- $S$ : a chain state $\langle\mathit{headers}, \mathit{utxo}\rangle$.
- $b$ : a serialized block (header, transaction list $b.\mathrm{vtx}$).
- Hypothesis $h_{ne}$ : $b.\mathrm{vtx} \ne [\,]$.
- Hypothesis $h_{vin}$ : every transaction $tx \in b.\mathrm{vtx}$ has $tx.\mathrm{vin} \ne [\,]$.

Both hypotheses are carried by the statement and absent from the conclusion.

## Conclusion

$$\mathrm{contextualCheckBlock}(S,b) = \mathrm{true} \iff \mathrm{ContextSpec}(S,b).$$

Common notation: $\mathit{height} = |S.\mathrm{headers}|$; $\mathrm{tipHeight} = |S.\mathrm{headers}| - 1$ (natural subtraction); $\mathit{cutoff} = \mathrm{mtp}(S)$ (sorted median of the first $11$ of the header times at heights $0..\mathrm{tipHeight}$ taken most recent first, default $0$) if $419328 \le \mathrm{tipHeight} + 1$, else $b.\mathrm{header.time}$ as an integer.

### Left side, unfolded

Boolean conjunction of:

1. every $tx \in b.\mathrm{vtx}$ satisfies $\mathrm{isFinalTx}(tx, \mathit{height}, \mathit{cutoff})$: true if $tx.\mathrm{nLockTime} = 0$; else true if $tx.\mathrm{nLockTime} < \mathit{height}$ when $tx.\mathrm{nLockTime} < 500\,000\,000$, respectively $tx.\mathrm{nLockTime} < \mathit{cutoff}$ otherwise; else true iff every input has $\mathrm{nSequence} = 4294967295$;
2. $227931 \le \mathrm{tipHeight}+1$ is false, **or** $\mathrm{heightScript}(\mathit{height})$ is a prefix of the scriptSig of the head input (default input with empty scriptSig) of the head transaction of $b.\mathrm{vtx}$ (default: the genesis coinbase); $\mathrm{heightScript}(n) = [0]$ if $n = 0$, $[0x50 + n]$ if $1 \le n \le 16$, otherwise the canonical push (length byte or PUSHDATA prefix) of the little-endian minimal signed script-number encoding of $n$;
3. $\mathrm{checkWitnessMalleation}(b, 481824 \le \mathrm{tipHeight}+1)$: with $\mathit{noWitness}$ = "no transaction of $b$ has an input with a non-empty witness": if the expectation flag is false, $\mathit{noWitness}$; if true, find the commitment index — the largest output index $p$ of the first transaction whose scriptPubKey has length $\ge 38$ and starts with bytes $6a\,24\,aa\,21\,a9\,ed$ (none if $b.\mathrm{vtx}$ is empty): if none, $\mathit{noWitness}$; else the witness stack of the first input (default input) of the first transaction (default genesis coinbase) must be exactly one element $\mathit{nonce}$ of length $32$ with $\mathrm{hash256}(\mathrm{blockWitnessMerkleRoot}(b) \mathbin{+\!\!+} \mathit{nonce})$ equal to bytes $6$ through $37$ of output $p$'s scriptPubKey, where $\mathrm{blockWitnessMerkleRoot}$ is the merkle root of $32$ zero bytes followed by the wtxids of the transactions after the first;
4. $\mathrm{blockWeight}(b) \le 4\,000\,000$, where $\mathrm{blockWeight}(b) = 3\cdot|\mathrm{serBlock}(\mathrm{false},b)| + |\mathrm{serBlock}(\mathrm{true},b)|$.

### Right side, unfolded

$\mathrm{ContextSpec}(S,b)$ is the conjunction of:

1. $\forall tx \in b.\mathrm{vtx},\ \mathrm{isFinalTx}(tx, \mathit{height}, \mathit{cutoff}) = \mathrm{true}$ (same function);
2. $227931 \le \mathrm{tipHeight}+1 \Rightarrow \forall cb \in \mathrm{take}_1(b.\mathrm{vtx}),\ \forall i \in \mathrm{take}_1(cb.\mathrm{vin}),\ \mathrm{heightScript}(\mathit{height})$ is a prefix of $i.\mathrm{scriptSig}$;
3. $\mathrm{checkWitnessMalleation}(b, 481824 \le \mathrm{tipHeight}+1) = \mathrm{true}$ (same function);
4. $\mathrm{blockWeight}(b) \le 4\,000\,000$.

The two sides differ only in clause 2, where the executable side uses head-with-default and the specification quantifies over the (at most one) first transaction and its (at most one) first input.

## Edge cases silently included

The hypotheses rule out exactly the cases where clause 2 differs (empty $b.\mathrm{vtx}$, or a first transaction with no inputs); empty header list ($\mathrm{tipHeight}=0$, median $0$); $b.\mathrm{header.time}$ unbounded; $tx.\mathrm{nLockTime}$ and $\mathrm{nSequence}$ unbounded naturals compared exactly; no coinbase or $\mathrm{checkBlock}$ assumption (the "first transaction" need not be a coinbase).
