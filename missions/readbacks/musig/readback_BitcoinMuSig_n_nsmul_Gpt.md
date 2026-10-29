# Read-back: `BitcoinMuSig.n_nsmul_Gpt`

Source file: `Thm_BitcoinMuSig_n_nsmul_Gpt.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** There are no variables and no hypotheses. In the group $W(\mathbb{F}_p)$, the $n$-fold sum of $G_{\mathrm{pt}}$ is the point at infinity:
$$n\cdot G_{\mathrm{pt}} = \underbrace{G_{\mathrm{pt}} + \dots + G_{\mathrm{pt}}}_{n} = 0 .$$
Nothing is asserted about smaller multiples.

## Definitions used, unfolded

### Constants

- $p = 2^{256} - 2^{32} - 977$ is a fixed natural number (the field modulus).
- $n = \mathtt{0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141}$ is a fixed natural number (written in hexadecimal).
- $G_x = \mathtt{0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798}$ and $G_y = \mathtt{0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8}$ are fixed natural numbers ($G_y$ is even: its last hexadecimal digit is $8$).

### The Mathlib curve $W$ and its point group $W(\mathbb{F}_p)$

- $\mathbb{F}_p$ denotes Mathlib's $\mathbb{Z}/p\mathbb{Z}$. For a natural number $x$, $(x : \mathbb{F}_p)$ is its residue $x \bmod p$. The definition file registers, as a global instance, the fact that $p$ is prime (proved there by a Lucas–Pratt certificate); this instance is what makes $\mathbb{Z}/p\mathbb{Z}$ a field, which Mathlib needs to put a group structure on curve points.
- $W$ is the Weierstrass curve over $\mathbb{F}_p$ with coefficients $a_1 = a_2 = a_3 = a_4 = 0$ and $a_6 = 7$, i.e. the curve
$$y^2 = x^3 + 7 .$$
- $W(\mathbb{F}_p)$ is Mathlib's type of points of $W$: a point is either the point at infinity, written $0$, or an affine point $(x, y) \in \mathbb{F}_p^2$ with $y^2 = x^3 + 7$ (carrying a proof that it is nonsingular). It is equipped with Mathlib's chord-and-tangent addition, which makes it an additive commutative group with neutral element $0$ and negation $-(x, y) = (x, -y)$, $-0 = 0$.
- For $k \in \mathbb{N}$ and $P \in W(\mathbb{F}_p)$, $k \cdot P = P + \dots + P$ ($k$ summands, $0 \cdot P = 0$). For $k \in \mathbb{Z}$, $k \cdot P$ is the usual integer multiple ($k \cdot P = -(|k|\cdot P)$ for $k<0$).
- $G_{\mathrm{pt}} \in W(\mathbb{F}_p)$ is the affine point $(G_x \bmod p,\ G_y \bmod p)$.

