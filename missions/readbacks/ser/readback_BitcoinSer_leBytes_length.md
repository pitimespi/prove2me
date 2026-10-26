# Read-back: `BitcoinSer.leBytes_length`

**Binders and hypothesis.** Two natural numbers $k$ and $n$ are universally quantified, with no restriction whatsoever on either: $k$ may be $0$, and $n$ may be any natural number, including values at or above $2^{8k}$. There are no hypotheses.

**Conclusion.** The byte string $\texttt{leBytes}\;k\;n$ has length exactly $k$:
$$|\texttt{leBytes}\;k\;n| = k .$$

**Unfolding.** $\texttt{leBytes}$ is the little-endian fixed-width encoder from the definitions file: for $k = 0$ it returns the empty list; for $k + 1$ it returns the single byte $n \bmod 256$ followed by $\texttt{leBytes}\;k\;\lfloor n / 256 \rfloor$. The statement therefore says that this recursion produces one byte per unit of $k$, regardless of the value being encoded. In particular:

- for $k = 0$ the claim is that the empty list has length $0$;
- for $n \ge 2^{8k}$ the encoder truncates $n$ modulo $2^{8k}$ (the discarded high bits do not add bytes), and the claim is still that exactly $k$ bytes come out;
- for $n = 0$ the result is $k$ zero bytes, of length $k$.

Because $\texttt{ser8}$, $\texttt{ser16}$, $\texttt{ser32}$, $\texttt{ser64}$ are defined as $\texttt{leBytes}$ with $k = 1, 2, 4, 8$, and $\texttt{beBytes}\;k\;n$ is the reversal of $\texttt{leBytes}\;k\;n$, the statement entails (though it does not itself state) that those encoders produce $1, 2, 4, 8$ bytes and that $\texttt{beBytes}\;k\;n$ has length $k$. Likewise $\texttt{serInt64}$ and $\texttt{serInt32}$ are $\texttt{leBytes}$ with $k = 8, 4$ applied to a reduced natural number, so they would have lengths 8 and 4; again, this is a consequence, not the statement.

**What is not said.** The theorem says nothing about the *content* of the bytes: it does not say the value decodes back to $n$ (that is the separate statement `readLE_leBytes`, which carries the hypothesis $n < 2^{8k}$), and it does not say what happens to the high bits of an over-large $n$ beyond the fact that the length is unaffected. It does not state that $\texttt{leVal}\;(\texttt{leBytes}\;k\;n) = n \bmod 2^{8k}$, nor anything about $\texttt{beBytes}$, $\texttt{ser32}$, etc. by name. It does not assert injectivity of $\texttt{leBytes}\;k$ on $[0, 2^{8k})$, nor that two different $n$ below $2^{8k}$ encode differently. It is purely a length statement for all $k, n \in \mathbb{N}$.
