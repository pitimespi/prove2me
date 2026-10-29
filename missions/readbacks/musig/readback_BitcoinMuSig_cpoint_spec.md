# Read-back: `BitcoinMuSig.cpoint_spec`

Source file: `Thm_BitcoinMuSig_cpoint_spec.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** For every byte string $b$ and every pair $P = (x, y)$ of natural numbers: if $\mathrm{cpoint}(b)$ succeeds and returns $(x, y)$, then

- $\mathrm{onCurve}(x, y)$ holds, i.e. $(y\cdot y) \bmod p = (x\cdot x\cdot x + 7) \bmod p$,
- $x < p$, and
- $y < p$.

Byte strings on which $\mathrm{cpoint}$ fails (wrong length, first byte not $2$ or $3$, abscissa $\ge p$, or no square root) satisfy the hypothesis for no $P$ and are not constrained.

## Definitions used, unfolded

### Constants

- $p = 2^{256} - 2^{32} - 977$ is a fixed natural number (the field modulus).
- $n = \mathtt{0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141}$ is a fixed natural number (written in hexadecimal).
- $G_x = \mathtt{0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798}$ and $G_y = \mathtt{0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8}$ are fixed natural numbers ($G_y$ is even: its last hexadecimal digit is $8$).

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

### Byte strings, hashing and point encodings

- A *byte string* is a finite list of bytes (values $0, \dots, 255$). $|b|$ is its length, $\Vert$ is concatenation. $\mathrm{take}_k(b)$ is the first $\min(k, |b|)$ bytes of $b$ and $\mathrm{drop}_k(b)$ is $b$ with its first $\min(k, |b|)$ bytes removed, so a slice of a too-short string is silently shorter (possibly empty).
- $\mathrm{beVal}(b) = \sum_{i=0}^{|b|-1} b_i \, 256^{\,|b|-1-i}$ is the big-endian value of $b$ (any length; $\mathrm{beVal}$ of the empty string is $0$).
- $\mathrm{be32}(x)$ is the $32$-byte big-endian encoding of $x \bmod 2^{256}$ (bits of $x$ above $2^{256}$ are silently dropped).
- For a pair $P = (x, y)$ of naturals: $\mathrm{xbytes}(P) = \mathrm{be32}(x)$; $\mathrm{hasEvenY}(P)$ holds iff $y \bmod 2 = 0$ (parity of the raw natural $y$, no reduction mod $p$); $\mathrm{cbytes}(P) = [c] \,\Vert\, \mathrm{be32}(x)$, a $33$-byte string whose first byte $c$ is $2$ if $\mathrm{hasEvenY}(P)$ and $3$ otherwise.
- $\mathrm{zero}_{33}$ is the string of $33$ zero bytes. $\mathrm{cbytesExt}(\infty) = \mathrm{zero}_{33}$ and $\mathrm{cbytesExt}(P) = \mathrm{cbytes}(P)$ for a pair $P$.
- $\mathrm{SHA256}$ is the executable SHA-256 function of the serialization definition file. $\mathrm{ascii}(s)$ is the UTF-8 byte string of a text string $s$. The tagged hash is
$$\mathrm{tagged}(s, m) = \mathrm{SHA256}\big(\mathrm{SHA256}(\mathrm{ascii}(s)) \,\Vert\, \mathrm{SHA256}(\mathrm{ascii}(s)) \,\Vert\, m\big).$$

### Parsing compressed points

- $\mathrm{liftXParity}(x, \mathit{odd})$ for a natural $x$ and a requested parity: let $y = (x^3 + 7)^{(p+1)/4} \bmod p$ (computed by $\mathrm{powMod}$; $(p+1)/4$ is natural-number division). If $y^2 \bmod p = (x^3 + 7) \bmod p$, the result is the pair $(x, y^\ast)$ where $y^\ast = y$ if the parity of $y$ is the requested one and $y^\ast = (p - y) \bmod p$ otherwise (if $y = 0$ then $y^\ast = 0$ whatever parity was requested); if not, the result is a failure.
- $\mathrm{cpoint}(b)$ parses a byte string as a compressed point. If $|b| \neq 33$ it fails. If $|b| = 33$, write $b = [t] \Vert r$ with $|r| = 32$: if $t \notin \{2, 3\}$ it fails; otherwise let $x = \mathrm{beVal}(r)$; if $x \ge p$ it fails, and if $x < p$ the result is $\mathrm{liftXParity}(x, \mathit{odd} = (t = 3))$ (which may itself fail). A successful result is a pair $(x, y)$ of naturals.
- **Important typing fact.** The result of $\mathrm{cpoint}$ has the same type as an executable point, and its failure value is literally the value $\infty$. So wherever $\mathrm{cpoint}(b)$ is used as an executable point, a parse failure *is* the point at infinity.
- $\mathrm{cpointExt}(b)$: if $b = \mathrm{zero}_{33}$ the result is "success with $\infty$"; otherwise it is "success with the pair $\mathrm{cpoint}(b)$" when $\mathrm{cpoint}(b)$ succeeds, and failure when it fails. (Here failure and $\infty$ are distinct outcomes.)

