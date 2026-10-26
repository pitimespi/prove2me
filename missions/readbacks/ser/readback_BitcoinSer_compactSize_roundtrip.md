# Read-back: `BitcoinSer.compactSize_roundtrip`

**Binders and hypothesis.** A natural number $n$, a byte string $\texttt{rest}$ (arbitrary, possibly empty), and the hypothesis
$$h : n < 2^{64}.$$

**Conclusion.** Reading a CompactSize **without** range check from the encoding of $n$ followed by $\texttt{rest}$ succeeds and yields $n$ and $\texttt{rest}$:
$$\texttt{readCompactSize}\;\mathrm{false}\;\big(\texttt{writeCompactSize}\;n \mathbin{+\!\!+} \texttt{rest}\big) = \mathrm{some}\,(n, \texttt{rest}).$$
The first argument of the reader is the Boolean `false`, i.e. the $\texttt{MAX\_SIZE}$ bound is **not** enforced in this statement.

**Unfolding the encoder.** $\texttt{writeCompactSize}\;n$ is: the single byte $n$ if $n < 253$; the byte $253$ followed by 2 little-endian bytes of $n$ if $253 \le n \le \mathrm{0xffff}$; the byte $254$ followed by 4 little-endian bytes if $\mathrm{0xffff} < n \le \mathrm{0xffffffff}$; and the byte $255$ followed by 8 little-endian bytes otherwise. Under $n < 2^{64}$ the 8-byte case does not truncate.

**Unfolding the decoder.** $\texttt{readCompactSize}\;\mathrm{false}\;s$ fails on empty $s$; otherwise it inspects the first byte $c$: if $c < 253$ the value is $c$; if $c = 253$ it reads 2 bytes as $v$ and fails if $v < 253$; if $c = 254$ it reads 4 bytes and fails if $v < \mathrm{0x10000}$; if $c = 255$ it reads 8 bytes and fails if $v < \mathrm{0x100000000}$; a short read in any of these fails. With the Boolean `false` the final range test is skipped, so the provisional result is returned as is. The theorem thus asserts, for every $n < 2^{64}$, that the prefix byte chosen by the encoder leads the decoder into the matching branch, that the fixed-width payload decodes back to $n$, that $n$ passes the corresponding canonicality threshold (which holds because the encoder chose the shortest form), and that the remaining bytes are exactly $\texttt{rest}$.

Boundary cases included by the quantifier: $n = 0$ (one zero byte), $n = 252$ (one byte), $n = 253$ (three bytes, value exactly at the lower canonical threshold), $n = \mathrm{0xffff}$ and $n = \mathrm{0x10000}$ (switch from 2 to 4 bytes), $n = \mathrm{0xffffffff}$ and $n = 2^{32}$ (switch to 8 bytes), and $n = 2^{64} - 1$. Values above $\texttt{MAX\_SIZE} = 2^{25}$ are included, since no range check is applied.

**What is not said.** Nothing is asserted for the range-checked reader ($rc = \mathrm{true}$): for $\texttt{MAX\_SIZE} < n < 2^{64}$ that reader returns no result, and the theorem is silent on it, while for $n \le \texttt{MAX\_SIZE}$ the range-checked result would agree but this is not stated. Nothing is asserted for $n \ge 2^{64}$, where the encoder truncates to $n \bmod 2^{64}$ and the decoder may either return the truncated value or fail the canonicality check. The converse ("every successful read comes from the canonical encoding") is a separate statement, `compactSize_canonical`. The theorem does not state the length of the encoding, nor that the decoder fails on malformed input. It is the one-directional round trip, for the unchecked reader only, under $n < 2^{64}$.
