# Read-back: `BitcoinBlock.work_increases`

## Binders and hypotheses

- $S$ : a chain state $\langle\mathit{headers},\mathit{utxo}\rangle$; $b$ : a serialized block; $\mathit{now} \in \mathbb{Z}$.
- $S'$ : a chain state; $\mathit{undo}$ : a block undo list.
- Hypothesis $h$ : $\mathrm{validate}(S, b, \mathit{now}) = \mathrm{accept}(S', \mathit{undo})$.

## Conclusion

$$\mathrm{chainWork}(S) < \mathrm{chainWork}(S'),$$
a strict inequality of natural numbers, where $\mathrm{chainWork}(T) = \sum_{h \in T.\mathrm{headers}} \mathrm{blockProof}(h.\mathrm{bits})$ and
$$\mathrm{blockProof}(\mathit{bits}) = \begin{cases} 0 & \text{if } \mathrm{deriveTarget}(\mathit{bits} \bmod 2^{32}) = \mathrm{none},\\ \left\lfloor \dfrac{2^{256} - 1 - t}{t + 1}\right\rfloor + 1 & \text{if } \mathrm{deriveTarget}(\mathit{bits} \bmod 2^{32}) = \mathrm{some}\,t, \end{cases}$$
with $\mathrm{deriveTarget}$ decoding the compact word (mantissa $=$ low $23$ bits, exponent $=$ top byte, left shift truncated modulo $2^{256}$) and returning none when the word is "negative" (mantissa $\ne 0$ and bit $0x00800000$ set), the value is $0$, the word "overflows", or the value exceeds $2^{224}-1$.

### Hypothesis, unfolded

$h$ holds exactly when: $\mathrm{checkHeaderPow}(b.\mathrm{header})$ is true (in particular $\mathrm{deriveTarget}(b.\mathrm{header.bits} \bmod 2^{32})$ is some $t$ with the header hash value $\le t$); $b.\mathrm{header.prevBlock} = \mathrm{tipHash}(S)$; the bits equal $\mathrm{requiredBits}(S)$; $\mathrm{mtp}(S) < b.\mathrm{header.time} \le \mathit{now} + 7200$; the version is not outdated; $\mathrm{checkBlock}(b)$ and $\mathrm{contextualCheckBlock}(S,b)$ hold; $\mathrm{connectBlock}(S,b) = \mathrm{some}(u, \mathit{undo})$; and $S' = \langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}],\ u\rangle$.

So the statement says: under those conditions, the sum of per-header proofs over $S'$'s headers — which are $S$'s headers followed by $b$'s header — strictly exceeds the sum over $S$'s headers; i.e. (since the sums differ exactly by $\mathrm{blockProof}(b.\mathrm{header.bits})$) that $\mathrm{blockProof}(b.\mathrm{header.bits}) > 0$.

## Edge cases silently included

$\mathit{undo}$ and $\mathit{now}$ matter only inside $h$; $\mathrm{blockProof}$ is $0$ for headers with an invalid compact target (possible among $S$'s existing headers, which are unconstrained); the formula $\lfloor(2^{256}-1-t)/(t+1)\rfloor + 1$ uses natural subtraction and floor division ($t \le 2^{224}-1$ whenever defined); the hypothesis may be unsatisfiable for a given $S$, making the claim vacuous.
