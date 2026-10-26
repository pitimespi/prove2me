# Read-back: `BitcoinBlock.bip30_history`

## Binders

- $S$ : a chain state $\langle \mathit{headers}, \mathit{utxo}\rangle$; only its header list is consulted here.
- $\mathit{height} \in \mathbb{N}$.
- $\mathit{hash}$ : a byte list (a list of 8-bit words, of any length).

There are no hypotheses.

## Conclusion

$$\mathrm{bip30Checked}(S, \mathit{height}, \mathit{hash}) = \mathrm{false} \iff \mathit{height} < 1983702 \;\wedge\; \Big(\mathrm{isBIP30Repeat}(\mathit{height}, \mathit{hash}) = \mathrm{true} \;\vee\; \exists h,\ S.\mathrm{headers}[227931] = \mathrm{some}\,h \wedge \mathrm{headerHash}(h) = \mathrm{bip34Hash}\Big).$$

### Left side, unfolded

$\mathrm{bip30Checked}(S,\mathit{height},\mathit{hash})$ is the Boolean
$$\big(\neg\,\mathrm{isBIP30Repeat}(\mathit{height},\mathit{hash}) \wedge \neg\,\mathit{bip34Ancestor}\big) \;\vee\; 1983702 \le \mathit{height},$$
where $\mathit{bip34Ancestor}$ is: if the header list of $S$ has an element at index $227931$, call it $h$, then "$\mathrm{headerHash}(h) = \mathrm{bip34Hash}$"; if the list is shorter, $\mathrm{false}$. $\mathrm{headerHash}(h)$ is the double-SHA256 of the 80-byte serialization of $h$ (version as 4 little-endian bytes of the value modulo $2^{32}$, previous hash bytes, merkle root bytes, then time, bits and nonce each as 4 little-endian bytes modulo $2^{32}$). $\mathrm{bip34Hash}$ is the fixed 32-byte constant beginning $b8\,08\,08\,9c\,\dots$ and ending with six zero bytes. The constant $1983702$ is `BIP34_IMPLIES_BIP30_LIMIT` and $227931$ is `BitcoinHeader.BIP34Height`.

$\mathrm{isBIP30Repeat}(\mathit{height},\mathit{hash})$ is $(\mathit{height} = 91842 \wedge \mathit{hash} = c_{91842}) \vee (\mathit{height} = 91880 \wedge \mathit{hash} = c_{91880})$ for two fixed 32-byte constants $c_{91842}$ (beginning $ec\,ca\,e0\,00\,\dots$) and $c_{91880}$ (beginning $21\,d7\,7c\,cb\,\dots$).

### Right side, unfolded

$\mathit{height} < 1983702$, and either $\mathrm{isBIP30Repeat}$ holds as just described, or there exists a header $h$ such that indexing $S.\mathrm{headers}$ at position $227931$ yields $h$ (so the list has length at least $227932$) and $\mathrm{headerHash}(h) = \mathrm{bip34Hash}$.

## Edge cases silently included

$\mathit{hash}$ of arbitrary length (then never equal to the 32-byte constants); a header list shorter than $227932$ (the ancestor clause is false on both sides); $\mathit{height} \ge 1983702$ makes the left side true regardless of the hash; the ledger of $S$ is irrelevant.
