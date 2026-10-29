# Read-back: `BitcoinMuSig.lagrange_interpolate_zero`

Source file: `Thm_BitcoinMuSig_lagrange_interpolate_zero.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** Let $S$ be a finite set of natural numbers with $i < n$ for every $i \in S$ (so the elements of $S$ have pairwise distinct residues mod $n$; $0 \in S$ is allowed; $S$ may be empty), and let $f \in (\mathbb{Z}/n)[X]$ be a polynomial with $\deg f < |S|$ (i.e. $f = 0$, or $f \neq 0$ and $\deg f \le |S| - 1$; for $S = \emptyset$ only $f = 0$ qualifies). Then, in $\mathbb{Z}/n$,
$$\sum_{i \in S} \lambda_i^S \, f(i) = f(0),$$
where $f(i)$ is $f$ evaluated at the residue $(i : \mathbb{Z}/n)$, $f(0)$ is $f$ evaluated at $0$, and
$$\lambda_i^S = \prod_{j \in S\setminus\{i\}} (j : \mathbb{Z}/n)\,\big((j:\mathbb{Z}/n) - (i:\mathbb{Z}/n)\big)^{-1}$$
with Mathlib's total inverse on $\mathbb{Z}/n$ (no primality of $n$ is assumed as a hypothesis or instance in the statement).

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

