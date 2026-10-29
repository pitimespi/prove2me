# Read-back: `BitcoinMuSig.frost_partialSigAgg`

Source file: `Thm_BitcoinMuSig_frost_partialSigAgg.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** Let $\iota$ be an arbitrary index type, $K$ an arbitrary commutative ring and $M$ an arbitrary additive commutative group with a $K$-module structure. Let $S$ be any finite subset of $\iota$ (possibly empty), $G \in M$ arbitrary, $D, E, Y : \iota \to M$ arbitrary families of elements of $M$, $\rho, \mathit{lam}, z : \iota \to K$ arbitrary families of scalars, and $c \in K$ arbitrary. Assume that for every $i \in S$
$$z_i\, G = D_i + \rho_i E_i + (c\,\mathit{lam}_i)\, Y_i .$$
Then
$$\Big(\sum_{i \in S} z_i\Big) G = \sum_{i \in S}\big(D_i + \rho_i E_i\big) + c \sum_{i \in S} \mathit{lam}_i\, Y_i .$$
No relation between $\mathit{lam}$, $Y$, $G$ and anything else is assumed; values at indices outside $S$ play no role; for $S = \emptyset$ both sides are $0$.

## Definitions used, unfolded

### The generic algebraic setting

- $\iota$ (where present) is an arbitrary type of indices, with no structure assumed (it may be empty, infinite, etc.).
- $K$ is an arbitrary commutative ring (with $1$; it may be the zero ring).
- $M$ is an arbitrary additive commutative group equipped with a $K$-module structure: a scalar multiplication $K \times M \to M$, written $kx$, satisfying the module axioms with respect to the given addition of $M$ ($1x = x$, $(kl)x = k(lx)$, $k(x+y) = kx + ky$, $(k+l)x = kx + lx$, $0x = 0$, $k0 = 0$). $M$ may be the trivial group.
- A finite set $S$ of indices (where present) may be empty; empty sums are $0$.
- Nothing from the Bitcoin definition files enters this statement: in particular, the letter $G$ is a universally quantified element of $M$, not the secp256k1 generator.

