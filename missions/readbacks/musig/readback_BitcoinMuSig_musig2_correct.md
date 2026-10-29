# Read-back: `BitcoinMuSig.musig2_correct`

Source file: `Thm_BitcoinMuSig_musig2_correct.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** Let $\iota$ be an arbitrary index type, $K$ an arbitrary commutative ring and $M$ an arbitrary additive commutative group with a $K$-module structure. For every finite set $S \subseteq \iota$ (possibly empty), every $G \in M$, all families $d, k_1, k_2, a : \iota \to K$ (written $d_i, k_{1,i}, k_{2,i}, a_i$) and all scalars $b, e, g, \mathit{gacc}, \mathit{tacc}, \varepsilon \in K$ (no hypotheses),
$$\Big(\sum_{i\in S}\big(\varepsilon k_{1,i} + b(\varepsilon k_{2,i}) + e\,a_i\,(g\cdot\mathit{gacc}\cdot d_i)\big) + e\,g\,\mathit{tacc}\Big) G$$
$$= \varepsilon\Big(\Big(\sum_{i\in S} k_{1,i}\,G\Big) + b\Big(\sum_{i\in S} k_{2,i}\,G\Big)\Big) + e\Big(g\Big(\mathit{gacc}\Big(\sum_{i\in S} a_i\,(d_i\,G)\Big) + \mathit{tacc}\,G\Big)\Big).$$
On the left, the term $e\,g\,\mathit{tacc}$ is added once, outside the sum over $S$. On the right, $\mathit{tacc}\,G$ is added once to $\mathit{gacc}$ times the sum (it is not inside the sum, and $\mathit{gacc}$ does not multiply it).

## Definitions used, unfolded

### The generic algebraic setting

- $\iota$ (where present) is an arbitrary type of indices, with no structure assumed (it may be empty, infinite, etc.).
- $K$ is an arbitrary commutative ring (with $1$; it may be the zero ring).
- $M$ is an arbitrary additive commutative group equipped with a $K$-module structure: a scalar multiplication $K \times M \to M$, written $kx$, satisfying the module axioms with respect to the given addition of $M$ ($1x = x$, $(kl)x = k(lx)$, $k(x+y) = kx + ky$, $(k+l)x = kx + lx$, $0x = 0$, $k0 = 0$). $M$ may be the trivial group.
- A finite set $S$ of indices (where present) may be empty; empty sums are $0$.
- Nothing from the Bitcoin definition files enters this statement: in particular, the letter $G$ is a universally quantified element of $M$, not the secp256k1 generator.

