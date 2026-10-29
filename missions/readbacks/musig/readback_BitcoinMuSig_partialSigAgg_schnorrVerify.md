# Read-back: `BitcoinMuSig.partialSigAgg_schnorrVerify`

Source file: `Thm_BitcoinMuSig_partialSigAgg_schnorrVerify.lean` (one theorem; it builds on the MuSig definition file, which itself uses the secp256k1 signature and Taproot definition files).

**Statement.** Let $ctx = (\mathit{aggnonce}, pks, \mathit{tweaks}, \mathit{msg})$ be any session context (any byte strings, any list of keys, any list of (tweak, x-only flag) pairs of any length, any message), and let
$$\mathit{sigs} = \big[(\mathit{psig}_1, pn_1, pk_1),\ \dots,\ (\mathit{psig}_u, pn_u, pk_u)\big]$$
be a list of triples of byte strings (a partial signature, a public nonce, a public key; repetitions allowed). Assume all of the following.

1. **Non-empty:** $u \ge 1$.
2. **Keys match:** $pks = [pk_1, \dots, pk_u]$ exactly (same entries, same order, same multiplicities).
3. **Key torsion:** for every entry $pk$ of $pks$, $\ n \cdot \mathrm{tp}(\mathrm{cpoint}(pk)) = 0$ in the group $W(\mathbb{F}_p)$. Here $\mathrm{cpoint}(pk)$ is used as an executable point, so a key that fails to parse contributes the value $\infty$, for which $\mathrm{tp}(\infty) = 0$ and the condition holds automatically; for a key parsing to $(x, y)$, $\mathrm{tp}(x, y)$ is the point $(x \bmod p, y \bmod p)$ of $W(\mathbb{F}_p)$ if $\mathrm{onCurve}(x, y)$ and $0$ otherwise, and $n\cdot(\,\cdot\,)$ is the $n$-fold sum.
4. **Aggregate nonce:** $\mathrm{nonceAgg}(pn_1, \dots, pn_u)$ succeeds and is exactly the byte string $\mathit{aggnonce}$.
5. **Every partial signature verifies:** for each $i = 1, \dots, u$, $\ \mathrm{partialSigVerifyInternal}(\mathit{psig}_i, pn_i, pk_i, ctx) = \text{true}$.
6. **Non-degenerate nonce:** for every session-values record $sv$, if $\mathrm{getSessionValues}(ctx)$ succeeds with $sv$ then its raw aggregate nonce $R'$ is not $\infty$. (This quantifies over all records, but only the actual output of the deterministic function $\mathrm{getSessionValues}(ctx)$ is constrained; the hypothesis would hold vacuously if $\mathrm{getSessionValues}(ctx)$ failed, although hypothesis 5 with $u \ge 1$ already requires it to succeed, since $\mathrm{partialSigVerifyInternal}$ returns false when it fails.)

**Conclusion.** There exist a session-values record $sv = (Q, \mathit{gacc}, \mathit{tacc}, b, R', R, e)$ and a byte string $\mathit{sig}$ such that

- $\mathrm{getSessionValues}(ctx)$ succeeds with $sv$;
- $\mathrm{partialSigAgg}(\mathit{psig}_1, \dots, \mathit{psig}_u;\ ctx)$ succeeds with $\mathit{sig}$;
- $\mathrm{schnorrVerify}\big(\mathrm{xbytes}(Q),\ \mathit{msg},\ \mathit{sig}\big) = \text{true}$.

Since both functions are deterministic, $sv$ is the output of $\mathrm{getSessionValues}(ctx)$ and $\mathit{sig} = \mathrm{xbytes}(R) \Vert \mathrm{be32}(s)$ with $s = \big(\sum_i \mathrm{beVal}(\mathit{psig}_i) + e\,g\,\mathit{tacc}\big) \bmod n$ as computed by $\mathrm{partialSigAgg}$. The verification key is the $32$-byte big-endian encoding $\mathrm{be32}(Q_x)$ of the first coordinate of the (tweaked) aggregate key $Q$ held in the session values. All hypotheses concern only the public byte strings and the functions below; nothing is assumed about how the triples were produced.

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

### Executable negation

- $\mathrm{pneg}(\infty) = \infty$ and $\mathrm{pneg}(x, y) = \big(x,\ (p - y \bmod p) \bmod p\big)$: the first coordinate is kept as is (unreduced if it was), the second becomes the residue of $-y$ in $\{0, \dots, p-1\}$.

### From executable points to Mathlib points

- $\mathrm{toPoint}(P)$ takes values in $W(\mathbb{F}_p) \cup \{\mathsf{fail}\}$ (an optional Mathlib point):
  - $\mathrm{toPoint}(\infty) = 0$, the Mathlib point at infinity (a genuine point, *not* $\mathsf{fail}$);
  - $\mathrm{toPoint}(x, y) = (x \bmod p,\ y \bmod p) \in W(\mathbb{F}_p)$ if $\mathrm{onCurve}(x, y)$ holds;
  - $\mathrm{toPoint}(x, y) = \mathsf{fail}$ otherwise.
- $\mathrm{tp}(P) \in W(\mathbb{F}_p)$ is $\mathrm{toPoint}(P)$ with $\mathsf{fail}$ replaced by $0$. Thus $\mathrm{tp}(\infty) = 0$, $\mathrm{tp}(x, y) = (x \bmod p, y \bmod p)$ for on-curve pairs, and $\mathrm{tp}(x, y) = 0$ for every off-curve pair (an off-curve pair has the same image as $\infty$). Pairs differing by multiples of $p$ in their coordinates have the same image.
- $\mathrm{Valid}(P)$ means: if $P$ is a pair $(x, y)$ then $\mathrm{onCurve}(x, y)$ holds. $\infty$ is Valid. Validity does not require reduced coordinates.
- $\mathrm{Reduced}(P)$ means: if $P$ is a pair $(x, y)$ then $x < p$ and $y < p$. $\infty$ is Reduced. Reducedness does not require being on the curve.

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

### The MuSig2 (BIP327-style) algorithms of the definition file

Notation: $aP$ for a natural $a$ and an executable point $P$ means $\mathrm{pmul}(a, P)$; "fails" means the optional result is absent.

- **Key-aggregation context**: a record $(Q, \mathit{gacc}, \mathit{tacc})$ with $Q = (Q_x, Q_y)$ a pair of naturals (never $\infty$) and $\mathit{gacc}, \mathit{tacc}$ naturals.
- $\mathrm{hashKeys}(pk_1, \dots, pk_u) = \mathrm{tagged}(\text{"KeyAgg list"},\ pk_1 \Vert \cdots \Vert pk_u)$.
- $\mathrm{getSecondKey}(pks)$: $\mathrm{zero}_{33}$ if $pks$ is empty; otherwise the first entry of $pks$ (in list order) that differs from $pk_1$, or $\mathrm{zero}_{33}$ if every entry equals $pk_1$.
- $\mathrm{keyAggCoeff}(pks, pk) = 1$ if $pk = \mathrm{getSecondKey}(pks)$, and otherwise $\mathrm{beVal}\big(\mathrm{tagged}(\text{"KeyAgg coefficient"},\ \mathrm{hashKeys}(pks) \Vert pk)\big) \bmod n$. ($pk$ need not occur in $pks$.)
- $\mathrm{keyAggSum}(pks, \ell)$ for a list $\ell$ of byte strings: for $\ell$ empty it succeeds with $\infty$; for $\ell = pk :: \mathit{rest}$ it succeeds with $\mathrm{padd}\big(\mathrm{pmul}(\mathrm{keyAggCoeff}(pks, pk), \mathrm{cpoint}(pk)),\ \mathit{acc}\big)$ provided $\mathrm{cpoint}(pk)$ succeeds and $\mathrm{keyAggSum}(pks, \mathit{rest})$ succeeds with $\mathit{acc}$, and fails otherwise. For $\ell = (pk_1, \dots, pk_u)$ with parsed points $P_i$ and coefficients $a_i = \mathrm{keyAggCoeff}(pks, pk_i)$ this is the right-nested sum
$$\mathrm{padd}\big(a_1P_1,\ \mathrm{padd}(a_2P_2,\ \dots\ \mathrm{padd}(a_uP_u, \infty)\cdots)\big).$$
- $\mathrm{keyAgg}(pks)$: if $\mathrm{keyAggSum}(pks, pks)$ succeeds with a pair $Q$, the result is the context $(Q, 1, 0)$; it fails if some key does not parse or the sum is $\infty$ (in particular it fails for the empty list).
- $\mathrm{applyTweak}(ctx, \mathit{tweak}, \mathit{isXonly})$ with $ctx = (Q, \mathit{gacc}, \mathit{tacc})$: let $g = n - 1$ if $\mathit{isXonly}$ is true and $\mathrm{hasEvenY}(Q)$ is false, else $g = 1$; let $t = \mathrm{beVal}(\mathit{tweak})$ (the length of $\mathit{tweak}$ is not checked). If $t \ge n$ it fails. Otherwise let $Q' = \mathrm{padd}(gQ, tG)$; if $Q' = \infty$ it fails, else the result is $\big(Q',\ (g \cdot \mathit{gacc}) \bmod n,\ (t + g\cdot \mathit{tacc}) \bmod n\big)$.
- $\mathrm{applyTweaks}(ctx, [(tw_1, x_1), \dots, (tw_v, x_v)])$ applies $\mathrm{applyTweak}$ with $(tw_1, x_1)$, then $(tw_2, x_2)$, etc., failing as soon as one step fails; with no tweaks it returns $ctx$.
- $\mathrm{keyAggTweaked}(pks, \mathit{tweaks})$: $\mathrm{keyAgg}(pks)$ followed by $\mathrm{applyTweaks}$; fails if either fails.
- $\mathrm{nonceSum}(j, \ell)$ for $j \in \mathbb{N}$ and a list $\ell$ of byte strings: for $\ell$ empty it succeeds with $\infty$; for $\ell = pn :: \mathit{rest}$ it succeeds with $\mathrm{padd}(R, \mathit{acc})$ provided $R = \mathrm{cpoint}(\mathrm{take}_{33}(\mathrm{drop}_{33j}(pn)))$ succeeds (a pair; an individual nonce half can never be $\infty$) and $\mathrm{nonceSum}(j, \mathit{rest})$ succeeds with $\mathit{acc}$, and fails otherwise. The total length of each $pn$ is not checked; for $j = 0$ its first $33$ bytes are used, for $j = 1$ its bytes $33$ to $65$.
- $\mathrm{nonceAgg}(pn_1, \dots, pn_u)$: if $\mathrm{nonceSum}(0, \cdot)$ succeeds with $R_1$ and $\mathrm{nonceSum}(1, \cdot)$ succeeds with $R_2$, the result is the $66$-byte string $\mathrm{cbytesExt}(R_1) \Vert \mathrm{cbytesExt}(R_2)$; otherwise it fails. For the empty list it is $\mathrm{zero}_{33} \Vert \mathrm{zero}_{33}$.
- **Session context** $ctx$: a record of a byte string $\mathit{aggnonce}$, a list $pks$ of byte strings, a list $\mathit{tweaks}$ of (byte string, boolean) pairs, and a byte string $\mathit{msg}$. No constraint relates the fields.
- **Session values**: a record $(Q, \mathit{gacc}, \mathit{tacc}, b, R', R, e)$ where $Q$ and $R$ are pairs of naturals, $R'$ is an executable point, and $\mathit{gacc}, \mathit{tacc}, b, e$ are naturals.
- $\mathrm{getSessionValues}(ctx)$:
  1. Compute $\mathrm{keyAggTweaked}(pks, \mathit{tweaks})$; if it fails, fail; else call the result $(Q, \mathit{gacc}, \mathit{tacc})$.
  2. $b = \mathrm{beVal}\big(\mathrm{tagged}(\text{"MuSig/noncecoef"},\ \mathit{aggnonce} \Vert \mathrm{xbytes}(Q) \Vert \mathit{msg})\big) \bmod n$ (the whole $\mathit{aggnonce}$, whatever its length).
  3. $R_1 = \mathrm{cpointExt}(\mathrm{take}_{33}(\mathit{aggnonce}))$ and $R_2 = \mathrm{cpointExt}(\mathrm{take}_{33}(\mathrm{drop}_{33}(\mathit{aggnonce})))$; if either fails, fail. Each is $\infty$ (when its slice is $\mathrm{zero}_{33}$) or a parsed pair.
  4. $R' = \mathrm{padd}(R_1, \mathrm{pmul}(b, R_2))$.
  5. $R = (G_x, G_y)$ if $R' = \infty$, otherwise $R = R'$.
  6. $e = \mathrm{beVal}\big(\mathrm{tagged}(\text{"BIP0340/challenge"},\ \mathrm{xbytes}(R) \Vert \mathrm{xbytes}(Q) \Vert \mathit{msg})\big) \bmod n$.
  7. Succeed with $(Q, \mathit{gacc}, \mathit{tacc}, b, R', R, e)$.
- $\mathrm{partialSigVerifyInternal}(\mathit{psig}, \mathit{pubnonce}, pk, ctx)$ is a boolean:
  1. If $\mathrm{getSessionValues}(ctx)$ fails, false; otherwise use its values $(Q, \mathit{gacc}, \mathit{tacc}, b, R', R, e)$.
  2. Let $s = \mathrm{beVal}(\mathit{psig})$. If $|\mathit{psig}| \neq 32$ or $s \ge n$, false.
  3. Let $R_1 = \mathrm{cpoint}(\mathrm{take}_{33}(\mathit{pubnonce}))$, $R_2 = \mathrm{cpoint}(\mathrm{take}_{33}(\mathrm{drop}_{33}(\mathit{pubnonce})))$, $P = \mathrm{cpoint}(pk)$; if any of the three fails, false.
  4. If $pk$ is not an entry of $pks$, false.
  5. $R_e' = \mathrm{padd}(R_1, \mathrm{pmul}(b, R_2))$; $R_e = R_e'$ if $\mathrm{hasEvenY}(R)$, else $R_e = \mathrm{pneg}(R_e')$.
  6. $a = \mathrm{keyAggCoeff}(pks, pk)$; $g = 1$ if $\mathrm{hasEvenY}(Q)$, else $g = n - 1$; $g' = (g \cdot \mathit{gacc}) \bmod n$.
  7. The result is true iff the executable points
  $$\mathrm{pmul}(s, G) \quad\text{and}\quad \mathrm{padd}\big(R_e,\ \mathrm{pmul}((e \cdot a \cdot g') \bmod n,\ P)\big)$$
  are literally equal.
- $\mathrm{partialSigAgg}(\mathit{psig}_1, \dots, \mathit{psig}_u; ctx)$:
  1. If $\mathrm{getSessionValues}(ctx)$ fails, fail; otherwise use its values.
  2. If some $\mathit{psig}_i$ has $|\mathit{psig}_i| \neq 32$ or $\mathrm{beVal}(\mathit{psig}_i) \ge n$, fail.
  3. $g = 1$ if $\mathrm{hasEvenY}(Q)$, else $g = n - 1$.
  4. $s = \big(\sum_i \mathrm{beVal}(\mathit{psig}_i) + e \cdot g \cdot \mathit{tacc}\big) \bmod n$ (empty sum $= 0$).
  5. Succeed with the $64$-byte string $\mathrm{xbytes}(R) \Vert \mathrm{be32}(s)$.

### BIP340-style Schnorr verification

- $\mathrm{liftX}(x)$: if $x < p$ it is $\mathrm{liftXParity}(x, \text{even})$, otherwise it fails.
- $\mathrm{schnorrVerify}(pk_{32}, \mathit{msg}, \mathit{sig})$ is a boolean:
  1. If $|pk_{32}| \neq 32$ or $|\mathit{sig}| \neq 64$, false.
  2. $r = \mathrm{beVal}(\text{first 32 bytes of } \mathit{sig})$, $s = \mathrm{beVal}(\text{last 32 bytes of } \mathit{sig})$. If $r \ge p$ or $s \ge n$, false.
  3. $P = \mathrm{liftX}(\mathrm{beVal}(pk_{32}))$; if it fails, false.
  4. $e = \mathrm{beVal}\big(\mathrm{tagged}(\text{"BIP0340/challenge"},\ \mathrm{take}_{32}(\mathit{sig}) \Vert pk_{32} \Vert \mathit{msg})\big) \bmod n$.
  5. $T = \mathrm{padd}\big(\mathrm{pmul}(s, G),\ \mathrm{pmul}((n - e) \bmod n,\ P)\big)$. If $T = \infty$, false; if $T = (t_x, t_y)$, the result is true iff $t_y$ is even and $t_x = r$.

