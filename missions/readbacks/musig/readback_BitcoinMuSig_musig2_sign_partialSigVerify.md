# Read-back: `BitcoinMuSig.musig2_sign_partialSigVerify`

Source file: `Thm_BitcoinMuSig_musig2_sign_partialSigVerify.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** Let $K$ be an arbitrary commutative ring and $M$ an arbitrary additive commutative group with a $K$-module structure. For every $G \in M$ and all scalars $d, k_1, k_2, a, b, e, g, \mathit{gacc}, \varepsilon \in K$ (no hypotheses),
$$\big(\varepsilon k_1 + b(\varepsilon k_2) + e\,a\,(g\cdot\mathit{gacc}\cdot d)\big)\, G = \varepsilon\big(k_1 G + b\,(k_2 G)\big) + \big(e\,a\,(g\cdot\mathit{gacc})\big)(d\,G).$$

## Definitions used, unfolded

### The generic algebraic setting

- $\iota$ (where present) is an arbitrary type of indices, with no structure assumed (it may be empty, infinite, etc.).
- $K$ is an arbitrary commutative ring (with $1$; it may be the zero ring).
- $M$ is an arbitrary additive commutative group equipped with a $K$-module structure: a scalar multiplication $K \times M \to M$, written $kx$, satisfying the module axioms with respect to the given addition of $M$ ($1x = x$, $(kl)x = k(lx)$, $k(x+y) = kx + ky$, $(k+l)x = kx + lx$, $0x = 0$, $k0 = 0$). $M$ may be the trivial group.
- A finite set $S$ of indices (where present) may be empty; empty sums are $0$.
- Nothing from the Bitcoin definition files enters this statement: in particular, the letter $G$ is a universally quantified element of $M$, not the secp256k1 generator.

