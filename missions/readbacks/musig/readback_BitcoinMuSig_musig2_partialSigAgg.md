# Read-back: `BitcoinMuSig.musig2_partialSigAgg`

Source file: `Thm_BitcoinMuSig_musig2_partialSigAgg.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** Let $\iota$ be an arbitrary index type, $K$ an arbitrary commutative ring and $M$ an arbitrary additive commutative group with a $K$-module structure. Let $S \subseteq \iota$ be any finite set (possibly empty), $G \in M$, $X, R_1, R_2 : \iota \to M$ arbitrary families (written $X_i, R_{1,i}, R_{2,i}$), $a, s : \iota \to K$ arbitrary families of scalars, $b, e, g, \mathit{gacc}, \mathit{tacc}, \varepsilon \in K$ arbitrary scalars, and $Q \in M$. Assume

1. $Q = \mathit{gacc}\Big(\sum_{i\in S} a_i X_i\Big) + \mathit{tacc}\,G$ (the $\mathit{tacc}\,G$ term is outside both the sum and the factor $\mathit{gacc}$);
2. for every $i \in S$: $\ s_i\,G = \varepsilon\big(R_{1,i} + b\,R_{2,i}\big) + \big(e\,a_i\,(g\cdot\mathit{gacc})\big) X_i$.

Then
$$\Big(\sum_{i\in S} s_i + e\,g\,\mathit{tacc}\Big) G = \varepsilon\Big(\sum_{i\in S} R_{1,i} + b\sum_{i\in S} R_{2,i}\Big) + e\,(g\,Q),$$
where on the left $e\,g\,\mathit{tacc}$ is added once, outside the sum. No other relation among the variables is assumed.

## Definitions used, unfolded

### The generic algebraic setting

- $\iota$ (where present) is an arbitrary type of indices, with no structure assumed (it may be empty, infinite, etc.).
- $K$ is an arbitrary commutative ring (with $1$; it may be the zero ring).
- $M$ is an arbitrary additive commutative group equipped with a $K$-module structure: a scalar multiplication $K \times M \to M$, written $kx$, satisfying the module axioms with respect to the given addition of $M$ ($1x = x$, $(kl)x = k(lx)$, $k(x+y) = kx + ky$, $(k+l)x = kx + lx$, $0x = 0$, $k0 = 0$). $M$ may be the trivial group.
- A finite set $S$ of indices (where present) may be empty; empty sums are $0$.
- Nothing from the Bitcoin definition files enters this statement: in particular, the letter $G$ is a universally quantified element of $M$, not the secp256k1 generator.

