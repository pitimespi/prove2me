# Read-back: `BitcoinBlock.checkBlock_iff`

## Binders

- $b$ : a serialized block: a header $b.\mathrm{header}$ (version $\in \mathbb{Z}$; prevBlock, merkleRoot byte lists; time, bits, nonce $\in\mathbb{N}$) and a transaction list $b.\mathrm{vtx}$ (each transaction: version $\in\mathbb{N}$, input list, output list, lock time $\in \mathbb{N}$; an input has a prevout $\langle\text{hash bytes}, n\in\mathbb{N}\rangle$, a scriptSig, a sequence $\in\mathbb{N}$ and a witness stack; an output has a value $\in \mathbb{Z}$ and a scriptPubKey).

There are no hypotheses.

## Conclusion

$$\mathrm{checkBlock}(b) = \mathrm{true} \iff \mathrm{checkHeaderPow}(b.\mathrm{header}) = \mathrm{true} \;\wedge\; \mathrm{BlockSpec}(b).$$

### Left side, unfolded

$\mathrm{checkBlock}(b)$ is the Boolean conjunction (in source order) of:

1. $\mathrm{checkHeaderPow}(b.\mathrm{header})$: the little-endian value of the double-SHA256 of the serialized header is at most the target decoded (with truncation modulo $2^{256}$) from $b.\mathrm{header.bits} \bmod 2^{32}$, and that compact word is not negative, not zero-valued, not overflowing, and decodes to at most $2^{224}-1$;
2. the first component of $\mathrm{blockMerkleRoot}(b)$ equals $b.\mathrm{header.merkleRoot}$, where $\mathrm{blockMerkleRoot}(b)$ runs the merkle loop on the list of txids (double-SHA256 of the witness-stripped serialization) of $b.\mathrm{vtx}$: while more than one hash remains, flag "mutated" if some aligned pair (positions $2k, 2k+1$) is equal, then replace the list by the double-SHA256 of each concatenated aligned pair, an odd last element being concatenated with itself; the root is the single remaining hash, or $32$ zero bytes for an empty list;
3. the second component (the mutated flag) of $\mathrm{blockMerkleRoot}(b)$ is false;
4. $b.\mathrm{vtx}$ is non-empty;
5. $4\cdot |b.\mathrm{vtx}| \le 4\,000\,000$;
6. $4\cdot|\mathrm{serBlock}(\mathrm{false}, b)| \le 4\,000\,000$, where $\mathrm{serBlock}(\mathrm{false},b)$ is the serialized header followed by the compact-size-prefixed list of witness-stripped transaction serializations;
7. $\mathrm{isCoinBase}$ of the head of $b.\mathrm{vtx}$, with the genesis coinbase as default for an empty list; $\mathrm{isCoinBase}(tx)$ means $tx.\mathrm{vin}$ is a one-element list whose prevout has hash equal to $32$ zero bytes and index $2^{32}-1$;
8. every transaction of $b.\mathrm{vtx}$ after the first is not a coinbase;
9. every transaction $tx$ of $b.\mathrm{vtx}$ satisfies $\mathrm{checkTransaction}(tx)$: $tx.\mathrm{vin}\ne[\,]$, $tx.\mathrm{vout}\ne[\,]$, $4\cdot|\mathrm{serTx}(\mathrm{false},tx)| \le 4\,000\,000$, the output loop succeeds (each value $\ge 0$ and $\le 2\,100\,000\,000\,000\,000$ and each running partial sum in $[0, 2.1\cdot 10^{15}]$), the prevouts of $tx.\mathrm{vin}$ are pairwise distinct, and if $\mathrm{isCoinBase}(tx)$ then the scriptSig length of the head of $tx.\mathrm{vin}$ (default input: empty prevout hash, index $0$, empty scriptSig, sequence $0$, empty witness) lies in $[2,100]$, otherwise no input of $tx$ has a null prevout;
10. $4 \cdot \sum_{tx \in b.\mathrm{vtx}} \mathrm{legacySigOpCount}(tx) \le 80\,000$, where $\mathrm{legacySigOpCount}(tx)$ sums, over every input scriptSig and every output scriptPubKey, the inaccurate sigop count: scan the script instruction by instruction (stopping at a parse failure or when the byte-length fuel runs out), adding $1$ for each `OP_CHECKSIG`/`OP_CHECKSIGVERIFY` byte and $20$ for each `OP_CHECKMULTISIG`/`OP_CHECKMULTISIGVERIFY` byte.

### Right side, unfolded

$\mathrm{checkHeaderPow}(b.\mathrm{header}) = \mathrm{true}$ as in item 1, and $\mathrm{BlockSpec}(b)$, the proposition:

- $b.\mathrm{vtx} \ne [\,]$;
- $(\mathrm{blockMerkleRoot}\,b).1 = b.\mathrm{header.merkleRoot}$ and $(\mathrm{blockMerkleRoot}\,b).2 = \mathrm{false}$;
- $4\cdot|b.\mathrm{vtx}| \le 4\,000\,000$ and $4\cdot|\mathrm{serBlock}(\mathrm{false},b)| \le 4\,000\,000$;
- every transaction in the first one element of $b.\mathrm{vtx}$ is a coinbase, and every transaction after the first is not;
- every $tx \in b.\mathrm{vtx}$ satisfies $\mathrm{TxSpec}(tx)$: $tx.\mathrm{vin}\ne[\,]$, $tx.\mathrm{vout}\ne[\,]$, $4\cdot|\mathrm{serTx}(\mathrm{false},tx)|\le 4\,000\,000$, every output value $v$ satisfies $0 \le v \le 2.1\cdot 10^{15}$, the sum of all output values is $\le 2.1\cdot10^{15}$, prevouts pairwise distinct, $\mathrm{isCoinBase}(tx) = \mathrm{true} \Rightarrow$ every input's scriptSig length is in $[2,100]$, and $\mathrm{isCoinBase}(tx) = \mathrm{false} \Rightarrow$ no input has a null prevout;
- $4\cdot\sum_{tx}\mathrm{legacySigOpCount}(tx) \le 80\,000$.

## Edge cases silently included

Empty $b.\mathrm{vtx}$ (left: item 4 fails, while item 7 would consult the genesis coinbase; right: first clause fails); the coinbase scriptSig bound is checked on the head input on the left versus all inputs on the right (a coinbase has exactly one input); partial-sum range on the left versus total-sum range on the right; unbounded $\mathrm{bits}$ reduced modulo $2^{32}$; no well-formedness of byte lengths (hashes of length other than 32) is assumed.
