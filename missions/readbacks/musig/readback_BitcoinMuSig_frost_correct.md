# Read-back: `BitcoinMuSig.frost_correct`

Source file: `Thm_BitcoinMuSig_frost_correct.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** Let $M$ be any type equipped with an additive commutative group structure and a $\mathbb{Z}/n$-module structure (a scalar multiplication $\mathbb{Z}/n \times M \to M$, written $kx$, satisfying the module axioms with respect to the addition of $M$; $M$ may be the trivial group). Let

- $G \in M$ be arbitrary (a universally quantified element of $M$, not the secp256k1 generator);
- $S$ be a finite set of natural numbers with $i < n$ for every $i \in S$ (so distinct elements of $S$ have distinct residues mod $n$; $0 \in S$ is allowed, and $S$ may be empty);
- $f \in (\mathbb{Z}/n)[X]$ be a polynomial with $\deg f < |S|$ (i.e. $f = 0$, or $\deg f \le |S| - 1$; for $S = \emptyset$ this forces $f = 0$);
- $D, E : \mathbb{N} \to M$ and $\rho, z : \mathbb{N} \to \mathbb{Z}/n$ be arbitrary families (written $D_i, E_i, \rho_i, z_i$), and $c \in \mathbb{Z}/n$ arbitrary.

Assume that for every $i \in S$
$$z_i\, G = D_i + \rho_i E_i + \big(c\,\lambda_i^S\big)\big(f(i)\, G\big),$$
where $f(i)$ means $f$ evaluated at the residue $(i : \mathbb{Z}/n)$ and $\lambda_i^S = \mathrm{lagrangeCoeff}(S, i) \in \mathbb{Z}/n$. Then
$$\Big(\sum_{i \in S} z_i\Big) G = \sum_{i \in S} \big(D_i + \rho_i E_i\big) + c\,\big(f(0)\, G\big).$$
All scalars and sums of scalars are computed in $\mathbb{Z}/n$. Values of $D, E, \rho, z$ at indices outside $S$ play no role. If $S = \emptyset$ (so $f = 0$) both sides are $0$.

## Definitions used, unfolded

### Constants

- $p = 2^{256} - 2^{32} - 977$ is a fixed natural number (the field modulus).
- $n = \mathtt{0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141}$ is a fixed natural number (written in hexadecimal).
- $G_x = \mathtt{0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798}$ and $G_y = \mathtt{0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8}$ are fixed natural numbers ($G_y$ is even: its last hexadecimal digit is $8$).

### Residues mod $n$, Lagrange coefficients and polynomials

- $\mathbb{Z}/n$ is Mathlib's $\mathbb{Z}/n\mathbb{Z}$; for a natural $i$, $(i : \mathbb{Z}/n)$ is its residue $i \bmod n$. Mathlib's inverse $x^{-1}$ on $\mathbb{Z}/n$ is a total function: it is the multiplicative inverse when $x$ is coprime to $n$, and $0^{-1} = 0$. (The definition file does not register primality of $n$ as an instance.)
- For a finite set $S \subseteq \mathbb{N}$ and $i \in \mathbb{N}$,
$$\lambda_i^S = \mathrm{lagrangeCoeff}(S, i) = \prod_{j \in S \setminus \{i\}} (j : \mathbb{Z}/n)\cdot\big((j : \mathbb{Z}/n) - (i : \mathbb{Z}/n)\big)^{-1} \in \mathbb{Z}/n,$$
where the subtraction is in $\mathbb{Z}/n$. The empty product is $1$ (e.g. $S = \{i\}$ or $S = \emptyset$), and $i$ need not belong to $S$ (then nothing is removed). A factor with $j \equiv i \pmod n$, $j \ne i$, would be $j \cdot 0^{-1} = 0$.
- For a polynomial $f \in (\mathbb{Z}/n)[X]$, $f(a)$ is its evaluation at $a \in \mathbb{Z}/n$. Its degree $\deg f$ takes values in $\{-\infty\} \cup \mathbb{N}$ with $\deg 0 = -\infty$, which is smaller than every natural number. So $\deg f < |S|$ means: $f = 0$, or $f \ne 0$ and $\deg f \le |S| - 1$. For $S = \emptyset$ it forces $f = 0$.
- For $x \in \mathbb{Z}/n$, $\mathrm{val}(x) \in \{0, 1, \dots, n-1\}$ is its canonical natural representative.

