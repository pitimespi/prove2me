# Read-back: `BitcoinSer.readLE_leBytes`

**Binders and hypothesis.** Two natural numbers $k$ and $n$, a byte string $\texttt{rest}$ (a finite list of 8-bit values, possibly empty), and one hypothesis
$$h : n < 2^{8k}.$$
No other restriction: $k$ may be $0$ (then the hypothesis forces $n = 0$), and $\texttt{rest}$ is arbitrary.

**Conclusion.** Decoding $k$ little-endian bytes from the concatenation of the $k$-byte encoding of $n$ with $\texttt{rest}$ succeeds and returns $n$ together with $\texttt{rest}$ as the unconsumed remainder:
$$\texttt{readLE}\;k\;\big(\texttt{leBytes}\;k\;n \mathbin{+\!\!+} \texttt{rest}\big) = \mathrm{some}\,(n, \texttt{rest}).$$

**Unfolding.** Here $\texttt{leBytes}\;k\;n$ is the list of $k$ bytes, least significant first, with byte $i$ equal to $\lfloor n / 256^i \rfloor \bmod 256$. The decoder $\texttt{readLE}\;k\;s$ returns "no result" when $|s| < k$, and otherwise returns the pair $(\texttt{leVal}(s[{:}k]),\, s[k{:}])$, where $\texttt{leVal}$ sums $b_i \cdot 256^i$ over the bytes of its argument (with $\texttt{leVal}([\,]) = 0$). Since the encoded prefix has length exactly $k$ (whatever $n$ is), the input has length $\ge k$ and the "short read" case cannot occur; the statement then amounts to two facts:

- $\texttt{leVal}\;(\texttt{leBytes}\;k\;n) = n$ whenever $n < 2^{8k}$ (the little-endian value of the $k$-byte truncated encoding recovers $n$ exactly, because no bits were lost);
- dropping the first $k$ bytes of $\texttt{leBytes}\;k\;n \mathbin{+\!\!+} \texttt{rest}$ leaves exactly $\texttt{rest}$.

Degenerate instance: $k = 0$ gives $n = 0$, $\texttt{leBytes}\;0\;0 = [\,]$, and $\texttt{readLE}\;0\;\texttt{rest} = \mathrm{some}\,(0, \texttt{rest})$ since $\texttt{leVal}$ of the empty prefix is $0$; the statement holds trivially there. The equality is an equality of optional pairs, so it asserts both success (not "no result") and the exact values of both components.

**What is not said.** Nothing is claimed when $n \ge 2^{8k}$: in that case $\texttt{leBytes}$ truncates and the decoder would return $n \bmod 2^{8k}$, which the statement does not mention. Nothing is claimed about decoding arbitrary byte strings (the converse direction "if $\texttt{readLE}\;k\;s = \mathrm{some}\,(n, r)$ then $s = \texttt{leBytes}\;k\;n \mathbin{+\!\!+} r$" is not stated, although for $\texttt{readLE}$ it would be true). The statement does not cover the signed readers $\texttt{readInt32}/\texttt{readInt64}$ paired with $\texttt{serInt32}/\texttt{serInt64}$, nor the big-endian $\texttt{beBytes}$. It does not say the decoder fails on short input. It is a single-direction round-trip for the unsigned little-endian codec under the exact bound $n < 2^{8k}$.
