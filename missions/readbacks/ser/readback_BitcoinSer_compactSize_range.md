# Read-back: `BitcoinSer.compactSize_range`

**Binders and hypothesis.** A Boolean $rc$, a byte string $b$, a natural number $n$, a byte string $\texttt{rest}$, and the hypothesis
$$h : \texttt{readCompactSize}\;rc\;b = \mathrm{some}\,(n, \texttt{rest}),$$
i.e. the CompactSize reader with range-check flag $rc$ succeeds on $b$ with value $n$ and remainder $\texttt{rest}$.

**Conclusion.** A conjunction of two statements:
$$n < 2^{64} \quad\text{and}\quad \big(rc = \mathrm{true} \;\Rightarrow\; n \le \texttt{MAX\_SIZE}\big),$$
where $\texttt{MAX\_SIZE} = \mathrm{0x02000000} = 2^{25} = 33\,554\,432$.

**Unfolding.** The first conjunct is unconditional in $rc$. The reader produces $n$ in one of four ways: the first byte itself (so $n \le 252$), or the little-endian value of the following 2, 4 or 8 bytes (so $n < 2^{16}$, $n < 2^{32}$, $n < 2^{64}$ respectively, since $\texttt{leVal}$ of $k$ bytes is below $2^{8k}$). Hence every successful read has $n < 2^{64}$. The statement asserts this strict bound; $n = 2^{64}$ is excluded, $n = 2^{64} - 1$ is not.

The second conjunct is an implication: *if* $rc$ is the Boolean true, then $n \le \texttt{MAX\_SIZE}$, with equality permitted. This reflects the reader's final test, which rejects precisely when $rc$ is true and $\texttt{MAX\_SIZE} < n$; so $n = \texttt{MAX\_SIZE}$ is an accepted value and the bound here is non-strict, matching. When $rc$ is false the implication is vacuously true and the second conjunct contributes nothing; in that case $n$ may be as large as $2^{64} - 1$ (the reader with $rc$ false does not reject large values), and the theorem gives only the first conjunct.

Note the shape of the bound: the conclusion says $n \le \texttt{MAX\_SIZE}$, not $n < \texttt{MAX\_SIZE}$; a reader comparing against an intent phrased with a strict bound should note this.

**What is not said.** The theorem does not say the reader succeeds on any particular input, nor that it fails above $\texttt{MAX\_SIZE}$ (it only bounds the value in the success case). It does not relate $n$ to the bytes of $b$ (that is `compactSize_canonical`). It does not bound $|\texttt{rest}|$ or relate it to $|b|$. It says nothing about canonicality of the encoding. For $rc = \mathrm{false}$ it does not assert any bound tighter than $2^{64}$. It concerns only the direct reader, not $\texttt{readList}$/$\texttt{readBytes}$ (although those call the reader with $rc$ true, so a consequence would be that list and byte-string lengths obtained through them are $\le \texttt{MAX\_SIZE}$; this is not stated).
