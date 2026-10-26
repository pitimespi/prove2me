# Read-back: `BitcoinBlock.checkTransaction_iff`

## Binders

- $tx$ : a serialized transaction: version $\in \mathbb{N}$, a list $tx.\mathrm{vin}$ of inputs (each with prevout $\langle \text{hash bytes}, n \in \mathbb{N}\rangle$, scriptSig bytes, sequence $\in \mathbb{N}$, witness stack), a list $tx.\mathrm{vout}$ of outputs (each with value $\in \mathbb{Z}$ and scriptPubKey bytes), and lock time $\in \mathbb{N}$.

There are no hypotheses.

## Conclusion

$$\mathrm{checkTransaction}(tx) = \mathrm{true} \iff \mathrm{TxSpec}(tx).$$

### Left side, unfolded

$\mathrm{checkTransaction}(tx)$ is the Boolean conjunction of:

1. $tx.\mathrm{vin}$ is non-empty;
2. $tx.\mathrm{vout}$ is non-empty;
3. $|\mathrm{serTx}(\mathrm{false}, tx)| \cdot 4 \le 4\,000\,000$, where $\mathrm{serTx}(\mathrm{false},tx)$ is the witness-free serialization (4-byte version modulo $2^{32}$, compact-size-prefixed inputs, compact-size-prefixed outputs, 4-byte lock time modulo $2^{32}$);
4. $\mathrm{outputsLoop}(tx.\mathrm{vout}, 0)$ returns a value: scanning outputs in order with accumulator starting at $0$, fail if an output value is $<0$, fail if it is $> 2\,100\,000\,000\,000\,000$, fail if the new accumulator $\mathit{acc} + v$ is outside $[0, 2.1\cdot 10^{15}]$, else continue; success returns the final accumulator;
5. the list of prevouts of $tx.\mathrm{vin}$ has no duplicates;
6. if $\mathrm{isCoinBase}(tx)$ (i.e. $tx.\mathrm{vin}$ is a single input whose prevout hash is 32 zero bytes and whose index is $4294967295$): the scriptSig length of the head of $tx.\mathrm{vin}$ (default input with empty scriptSig if the list were empty) satisfies $2 \le \ell \le 100$; otherwise every input of $tx$ has a non-null prevout (prevout hash $\ne 32$ zero bytes or index $\ne 4294967295$).

### Right side, unfolded

$\mathrm{TxSpec}(tx)$ is the conjunction:

- $tx.\mathrm{vin} \ne [\,]$;
- $tx.\mathrm{vout} \ne [\,]$;
- $|\mathrm{serTx}(\mathrm{false},tx)|\cdot 4 \le 4\,000\,000$;
- for every output $o$ of $tx$, $0 \le o.\mathrm{nValue} \le 2\,100\,000\,000\,000\,000$;
- $\mathrm{valueOut}(tx) \le 2\,100\,000\,000\,000\,000$, where $\mathrm{valueOut}(tx) = \sum_{o \in tx.\mathrm{vout}} o.\mathrm{nValue}$ (an integer sum, $0$ for no outputs);
- the prevouts of $tx.\mathrm{vin}$ are pairwise distinct;
- $\mathrm{isCoinBase}(tx) = \mathrm{true} \Rightarrow$ for every input $i$ of $tx$, $2 \le |i.\mathrm{scriptSig}| \le 100$;
- $\mathrm{isCoinBase}(tx) = \mathrm{false} \Rightarrow$ for every input $i$ of $tx$, $\mathrm{outPointNull}(i.\mathrm{prevout}) = \mathrm{false}$.

## Edge cases silently included

Empty input or output lists (both sides false); the left checks every running partial sum while the right checks each value and the total; the coinbase scriptSig bound is on the head input (left) versus all inputs (right), the two coinciding because a coinbase has exactly one input; hash bytes of arbitrary length are allowed (a prevout hash is "null" only when it is exactly 32 zero bytes).
