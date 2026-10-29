# Read-back: `BitcoinMuSig.valid_padd`

Source file: `Thm_BitcoinMuSig_valid_padd.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** For all executable points $P, Q$ that are Valid (each is $\infty$, or a pair $(x, y)$ of naturals with $y^2 \equiv x^3 + 7 \pmod p$; coordinates need not be below $p$), the executable sum $\mathrm{padd}(P, Q)$ is again Valid: it is $\infty$, or a pair $(x_3, y_3)$ with $y_3^2 \equiv x_3^3 + 7 \pmod p$.

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

### Executable points and their arithmetic

- An *executable point* is either the special value $\infty$ (the code's "no coordinates" value, which it uses for the point at infinity) or a pair $(x, y)$ of natural numbers of arbitrary size. Nothing in the type requires $x, y < p$ or that the pair lies on the curve. Equality of executable points is literal equality: both $\infty$, or equal pairs of natural numbers (so $(x, y)$ and $(x+p, y)$ are different executable points).
- **Curve test.** For naturals $x, y$: $\mathrm{onCurve}(x, y)$ holds iff
$$ (y \cdot y) \bmod p = (x \cdot x \cdot x + 7) \bmod p ,$$
i.e. $y^2 \equiv x^3 + 7 \pmod p$. Pairs with unreduced coordinates ($x \ge p$ or $y \ge p$) can pass this test.
- **Modular powers and inversion.** $\mathrm{powMod}(b, e, m)$ is a square-and-multiply loop; the definition file proves $\mathrm{powMod}(b, e, m) = b^e \bmod m$ for all naturals $b, e, m$. The field inverse is $\mathrm{finv}(a) = a^{p-2} \bmod p$; in particular $\mathrm{finv}(a) = 0$ when $p \mid a$.
- **Addition** $\mathrm{padd}(P, Q)$:
  - $\mathrm{padd}(\infty, Q) = Q$ and $\mathrm{padd}(P, \infty) = P$, returned unchanged (unreduced coordinates stay unreduced).
  - For $P = (x_1, y_1)$, $Q = (x_2, y_2)$ with $x_1 \equiv x_2 \pmod p$:
    - if $y_1 + y_2 \equiv 0 \pmod p$ the result is $\infty$;
    - otherwise (tangent branch, which uses only $x_1, y_1$):
    $$\lambda = \big(3x_1^2 \cdot \mathrm{finv}(2y_1 \bmod p)\big) \bmod p,\quad x_3 = \big(\lambda^2 + 2(p - x_1 \bmod p)\big) \bmod p,$$
    $$y_3 = \big(\lambda \cdot ((x_1 + p - x_3) \bmod p) + (p - y_1 \bmod p)\big) \bmod p,$$
    and the result is $(x_3, y_3)$.
  - For $P = (x_1, y_1)$, $Q = (x_2, y_2)$ with $x_1 \not\equiv x_2 \pmod p$ (chord branch):
    $$\lambda = \Big( \big((y_2 + p - y_1 \bmod p) \bmod p\big) \cdot \mathrm{finv}\big((x_2 + p - x_1 \bmod p) \bmod p\big) \Big) \bmod p,$$
    $$x_3 = \big(\lambda^2 + (p - x_1 \bmod p) + (p - x_2 \bmod p)\big) \bmod p,\quad y_3 = \big(\lambda \cdot ((x_1 + p - x_3) \bmod p) + (p - y_1 \bmod p)\big) \bmod p,$$
    and the result is $(x_3, y_3)$.
  - All subtractions are of natural numbers but never truncate here (the subtracted quantity never exceeds the other). Whenever both inputs are pairs, the output is $\infty$ or a pair with both coordinates $< p$.
- **Scalar multiplication** $\mathrm{pmul}(k, P)$ for $k \in \mathbb{N}$: a least-significant-bit-first double-and-add loop with a fuel of exactly $257$ iterations. Starting from $(k, P, \mathrm{acc} = \infty)$, each iteration does: if $k = 0$, stop and return $\mathrm{acc}$; otherwise replace $\mathrm{acc}$ by $\mathrm{padd}(\mathrm{acc}, P)$ if $k$ is odd (else keep it), then replace $P$ by $\mathrm{padd}(P, P)$ and $k$ by $\lfloor k/2 \rfloor$. When the $257$ iterations are exhausted the current $\mathrm{acc}$ is returned. Consequently only the $257$ lowest bits of $k$ are ever used: $\mathrm{pmul}(k, P) = \mathrm{pmul}(k \bmod 2^{257}, P)$. Also $\mathrm{pmul}(0, P) = \infty$ and $\mathrm{pmul}(k, \infty) = \infty$.
- $G$ denotes the executable point $(G_x, G_y)$.

### From executable points to Mathlib points

- $\mathrm{toPoint}(P)$ takes values in $W(\mathbb{F}_p) \cup \{\mathsf{fail}\}$ (an optional Mathlib point):
  - $\mathrm{toPoint}(\infty) = 0$, the Mathlib point at infinity (a genuine point, *not* $\mathsf{fail}$);
  - $\mathrm{toPoint}(x, y) = (x \bmod p,\ y \bmod p) \in W(\mathbb{F}_p)$ if $\mathrm{onCurve}(x, y)$ holds;
  - $\mathrm{toPoint}(x, y) = \mathsf{fail}$ otherwise.
- $\mathrm{tp}(P) \in W(\mathbb{F}_p)$ is $\mathrm{toPoint}(P)$ with $\mathsf{fail}$ replaced by $0$. Thus $\mathrm{tp}(\infty) = 0$, $\mathrm{tp}(x, y) = (x \bmod p, y \bmod p)$ for on-curve pairs, and $\mathrm{tp}(x, y) = 0$ for every off-curve pair (an off-curve pair has the same image as $\infty$). Pairs differing by multiples of $p$ in their coordinates have the same image.
- $\mathrm{Valid}(P)$ means: if $P$ is a pair $(x, y)$ then $\mathrm{onCurve}(x, y)$ holds. $\infty$ is Valid. Validity does not require reduced coordinates.
- $\mathrm{Reduced}(P)$ means: if $P$ is a pair $(x, y)$ then $x < p$ and $y < p$. $\infty$ is Reduced. Reducedness does not require being on the curve.

