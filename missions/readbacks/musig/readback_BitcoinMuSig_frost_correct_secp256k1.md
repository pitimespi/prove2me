# Read-back: `BitcoinMuSig.frost_correct_secp256k1`

Source file: `Thm_BitcoinMuSig_frost_correct_secp256k1.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** Let

- $S$ be a finite set of natural numbers with $i < n$ for every $i \in S$ ($0 \in S$ allowed, $S$ may be empty);
- $f \in (\mathbb{Z}/n)[X]$ with $\deg f < |S|$ (i.e. $f = 0$, or $\deg f \le |S| - 1$; for $S = \emptyset$ this forces $f = 0$);
- $D, E : \mathbb{N} \to W(\mathbb{F}_p)$ be arbitrary families of curve points (written $D_i, E_i$);
- $\rho, z : \mathbb{N} \to \mathbb{Z}/n$ be arbitrary families of residues and $c \in \mathbb{Z}/n$ arbitrary.

Write $\mathrm{val}(x) \in \{0, \dots, n-1\}$ for the canonical representative of $x \in \mathbb{Z}/n$, and $\lambda_i^S = \mathrm{lagrangeCoeff}(S, i)$. Assume that for every $i \in S$
$$\mathrm{val}(z_i)\cdot G_{\mathrm{pt}} = D_i + \mathrm{val}(\rho_i)\cdot E_i + \mathrm{val}\big(c\,\lambda_i^S\big)\cdot\Big(\mathrm{val}\big(f(i)\big)\cdot G_{\mathrm{pt}}\Big)$$
in $W(\mathbb{F}_p)$, where $f(i)$ is $f$ evaluated at the residue $(i : \mathbb{Z}/n)$, the product $c\,\lambda_i^S$ is computed in $\mathbb{Z}/n$ before taking $\mathrm{val}$, and "$\cdot$" is the natural-number multiple in the group. Then
$$\mathrm{val}\Big(\sum_{i\in S} z_i\Big)\cdot G_{\mathrm{pt}} = \sum_{i \in S}\big(D_i + \mathrm{val}(\rho_i)\cdot E_i\big) + \mathrm{val}(c)\cdot\Big(\mathrm{val}\big(f(0)\big)\cdot G_{\mathrm{pt}}\Big),$$
where $\sum_{i\in S} z_i$ is computed in $\mathbb{Z}/n$ (reduced mod $n$) before taking $\mathrm{val}$, and the right-hand sum is in the group $W(\mathbb{F}_p)$.

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

### Residues mod $n$, Lagrange coefficients and polynomials

- $\mathbb{Z}/n$ is Mathlib's $\mathbb{Z}/n\mathbb{Z}$; for a natural $i$, $(i : \mathbb{Z}/n)$ is its residue $i \bmod n$. Mathlib's inverse $x^{-1}$ on $\mathbb{Z}/n$ is a total function: it is the multiplicative inverse when $x$ is coprime to $n$, and $0^{-1} = 0$. (The definition file does not register primality of $n$ as an instance.)
- For a finite set $S \subseteq \mathbb{N}$ and $i \in \mathbb{N}$,
$$\lambda_i^S = \mathrm{lagrangeCoeff}(S, i) = \prod_{j \in S \setminus \{i\}} (j : \mathbb{Z}/n)\cdot\big((j : \mathbb{Z}/n) - (i : \mathbb{Z}/n)\big)^{-1} \in \mathbb{Z}/n,$$
where the subtraction is in $\mathbb{Z}/n$. The empty product is $1$ (e.g. $S = \{i\}$ or $S = \emptyset$), and $i$ need not belong to $S$ (then nothing is removed). A factor with $j \equiv i \pmod n$, $j \ne i$, would be $j \cdot 0^{-1} = 0$.
- For a polynomial $f \in (\mathbb{Z}/n)[X]$, $f(a)$ is its evaluation at $a \in \mathbb{Z}/n$. Its degree $\deg f$ takes values in $\{-\infty\} \cup \mathbb{N}$ with $\deg 0 = -\infty$, which is smaller than every natural number. So $\deg f < |S|$ means: $f = 0$, or $f \ne 0$ and $\deg f \le |S| - 1$. For $S = \emptyset$ it forces $f = 0$.
- For $x \in \mathbb{Z}/n$, $\mathrm{val}(x) \in \{0, 1, \dots, n-1\}$ is its canonical natural representative.

