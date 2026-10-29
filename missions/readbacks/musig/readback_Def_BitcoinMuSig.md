# Read-back: `Def_BitcoinMuSig.lean`

This file (namespace `BitcoinMuSig`) imports Mathlib and the secp256k1 signature and Taproot definition files. Below, the first section unfolds the imported definitions it relies on; the second section has one paragraph per declaration of the file, in file order (lemmas, private lemmas, the instance, definitions and record types). The file supplies proofs for all of its lemmas; this read-back only states what each asserts.

## Imported definitions, unfolded

### Constants (from the signature file)

- $p = 2^{256} - 2^{32} - 977$ and $n = \mathtt{0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141}$ are fixed natural numbers.
- $G_x = \mathtt{0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798}$ and $G_y = \mathtt{0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8}$ are fixed natural numbers ($G_y$ is even: its last hexadecimal digit is $8$).

### Modular exponentiation (from the signature file)

- $\mathrm{powModAux}(m, \mathit{fuel}, b, e, \mathit{acc})$: if $\mathit{fuel} = 0$ return $\mathit{acc}$; otherwise, if $e = 0$ return $\mathit{acc}$, else recurse with $\mathit{fuel} - 1$, base $b\cdot b \bmod m$, exponent $\lfloor e/2 \rfloor$ and accumulator $\mathit{acc}\cdot b \bmod m$ if $e$ is odd ($\mathit{acc}$ unchanged if $e$ is even).
- $\mathrm{powMod}(b, e, m) = \mathrm{powModAux}(m,\ e + 1,\ b \bmod m,\ e,\ 1 \bmod m)$. (In natural-number arithmetic $x \bmod 0 = x$.)
- $\mathrm{finv}(a) = \mathrm{powMod}(a, p - 2, p)$.

### Executable points (from the signature file)

- An *executable point* is either the special value $\infty$ (the code's "no coordinates" value, which it uses for the point at infinity) or a pair $(x, y)$ of natural numbers of arbitrary size. Nothing in the type requires $x, y < p$ or that the pair lies on the curve. Equality of executable points is literal equality: both $\infty$, or equal pairs of natural numbers (so $(x, y)$ and $(x+p, y)$ are different executable points).
- **Curve test.** For naturals $x, y$: $\mathrm{onCurve}(x, y)$ holds iff
$$ (y \cdot y) \bmod p = (x \cdot x \cdot x + 7) \bmod p ,$$
i.e. $y^2 \equiv x^3 + 7 \pmod p$. Pairs with unreduced coordinates ($x \ge p$ or $y \ge p$) can pass this test.
- **Modular inversion.** $\mathrm{finv}(a) = \mathrm{powMod}(a, p-2, p)$; the lemma $\mathrm{powMod\_eq}$ below gives $\mathrm{finv}(a) = a^{p-2} \bmod p$, in particular $\mathrm{finv}(a) = 0$ when $p \mid a$.
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

### Bytes, hashing and parsing (from the serialization, signature and Taproot files)

- A *byte string* is a finite list of bytes (values $0, \dots, 255$); $|b|$ is its length and $\Vert$ concatenation. $\mathrm{take}_k(b)$ is the first $\min(k, |b|)$ bytes, $\mathrm{drop}_k(b)$ removes the first $\min(k, |b|)$ bytes (slices of too-short strings are silently shorter).
- $\mathrm{beVal}(b) = \sum_{i=0}^{|b|-1} b_i\,256^{\,|b|-1-i}$ (big-endian value, any length; $0$ for the empty string).
- $\mathrm{be32}(x)$ (Taproot file) is the $32$-byte big-endian encoding of $x \bmod 2^{256}$ (higher bits silently dropped).
- $\mathrm{SHA256}$ is the executable SHA-256 of the serialization file; $\mathrm{ascii}(s)$ is the UTF-8 byte string of the text $s$; $\mathrm{taggedHash}(t, m) = \mathrm{SHA256}(\mathrm{SHA256}(t) \Vert \mathrm{SHA256}(t) \Vert m)$.
- $\mathrm{liftXParity}(x, \mathit{odd})$: let $y = \mathrm{powMod}(x^3 + 7, (p+1)/4, p)$ (natural-number division). If $y^2 \bmod p = (x^3 + 7) \bmod p$ the result is the pair $(x, y^\ast)$ with $y^\ast = y$ if the parity of $y$ is the requested one, else $y^\ast = (p - y) \bmod p$ (so $y^\ast = 0$ when $y = 0$, whatever was requested); otherwise it fails (returns $\infty$, the "no point" value).
- $\mathrm{parsePubkey}(b)$: fails on the empty string. For $b = [t] \Vert r$: if $|b| = 33$ and $t \in \{2, 3\}$, let $x = \mathrm{beVal}(r)$; return $\mathrm{liftXParity}(x, t = 3)$ if $x < p$, else fail. Else if $|b| = 65$ and $t \in \{4, 6, 7\}$, let $x = \mathrm{beVal}(\text{first 32 bytes of } r)$, $y = \mathrm{beVal}(\text{rest of } r)$; return $(x, y)$ if $x < p$, $y < p$, (for $t \in \{6, 7\}$) $y$ is odd iff $t = 7$, and $\mathrm{onCurve}(x, y)$; else fail. Otherwise fail. Failure is the value $\infty$.

## The declarations of the file, in order

**`powModAux_eq` (lemma).** For every natural modulus $m$ and all naturals $\mathit{fuel}, b, e, \mathit{acc}$: if $e < 2^{\mathit{fuel}}$ and $\mathit{acc} \bmod m = \mathit{acc}$ (which means $\mathit{acc} < m$ when $m > 0$, and is automatic when $m = 0$ because $x \bmod 0 = x$), then
$$\mathrm{powModAux}(m, \mathit{fuel}, b, e, \mathit{acc}) = (\mathit{acc}\cdot b^e) \bmod m .$$

**`powMod_eq` (lemma).** For all naturals $b, e, m$ (no hypotheses; $m = 0$ and $m = 1$ included), $\mathrm{powMod}(b, e, m) = b^e \bmod m$ (with $x \bmod 0 = x$, so for $m = 0$ this is $b^e$).

**`prime_of_cert` (lemma, Pratt step).** For naturals $q, a$ and a finite list $fs = [r_1, \dots, r_k]$ of naturals: if (i) $1 < q$, (ii) every $r \in fs$ is prime, (iii) $q - 1 = r_1 r_2 \cdots r_k$ (list product with multiplicity; the empty product is $1$), (iv) $\mathrm{powMod}(a, q - 1, q) = 1$, and (v) for every $r \in fs$, $\mathrm{powMod}(a, \lfloor (q-1)/r \rfloor, q) \neq 1$, then $q$ is prime.

**`prime_13331831` (private lemma).** The natural number $13331831$ is prime.

**`prime_173378833005251801` (private lemma).** The natural number $173378833005251801$ is prime.

**`prime_22149492674086928081353` (private lemma).** The natural number $22149492674086928081353$ is prime.

**`prime_132896956044521568488119` (private lemma).** The natural number $132896956044521568488119$ is prime.

**`prime_1206781` (private lemma).** The natural number $1206781$ is prime.

**`prime_7240687` (private lemma).** The natural number $7240687$ is prime.

**`prime_107590001` (private lemma).** The natural number $107590001$ is prime.

**`prime_255515944373312847190720520512484175977` (private lemma).** The natural number $255515944373312847190720520512484175977$ is prime.

**`prime_q5` (private lemma).** The natural number $q_5 = 205115282021455665897114700593932402728804164701536103180137503955397371$ is prime.

**`p_prime_cert` (lemma).** The natural number $p = 2^{256} - 2^{32} - 977$ is prime ($p \ge 2$ and its only positive divisors are $1$ and $p$). (Its docstring records the certificate $p - 1 = 2\cdot 3\cdot 7\cdot 13441\cdot q_5$ with witness $3$.)

**`instFactPrimeP` (instance).** Registers, for automatic type-class inference everywhere this file is imported, the fact that $p$ is prime. Through Mathlib this makes $\mathbb{F}_p := \mathbb{Z}/p\mathbb{Z}$ a field, which is required for the group structure on the points of $W$ below.

**`W` (definition).** $W$ is the Weierstrass curve in affine coordinates over $\mathbb{F}_p$ with coefficients $a_1 = a_2 = a_3 = a_4 = 0$ and $a_6 = 7$; its equation $y^2 + a_1xy + a_3y = x^3 + a_2x^2 + a_4x + a_6$ is
$$y^2 = x^3 + 7 .$$
Its type of points $W(\mathbb{F}_p)$ (Mathlib) consists of the point at infinity, written $0$, and the affine points $(x, y) \in \mathbb{F}_p^2$ satisfying the equation together with a proof of nonsingularity; with the field instance above it is an additive commutative group (chord-and-tangent law, neutral element $0$, $-(x,y) = (x, -y)$), and $k\cdot P$ denotes the $k$-fold sum for $k \in \mathbb{N}$ (integer multiples for $k \in \mathbb{Z}$).

**`W_Δ` (lemma).** The discriminant of $W$ (Mathlib's $\Delta = -b_2^2 b_8 - 8b_4^3 - 27b_6^2 + 9b_2b_4b_6$, which for these coefficients has $b_2 = b_4 = b_8 = 0$, $b_6 = 4a_6 = 28$) equals $-21168$ as an element of $\mathbb{F}_p$.

**`W_Δ_ne_zero` (lemma).** The discriminant of $W$ is nonzero in $\mathbb{F}_p$ (equivalently, $p \nmid 21168$).

**`equation_iff_onCurve` (lemma).** For all naturals $x, y$: the residues $(x \bmod p, y \bmod p)$ satisfy the equation of $W$ in $\mathbb{F}_p$ if and only if $\mathrm{onCurve}(x, y)$ is true, i.e. iff $(y\cdot y) \bmod p = (x\cdot x\cdot x + 7) \bmod p$.

**`nonsingular_of_onCurve` (lemma).** For all naturals $x, y$ with $\mathrm{onCurve}(x, y)$ true, the pair of residues $(x \bmod p, y \bmod p)$ is a nonsingular point of $W$ (Mathlib's notion: it satisfies the equation and the two partial derivatives of the defining polynomial do not both vanish there).

**`toPoint` (definition).** Converts an executable point to an optional Mathlib point, with values in $W(\mathbb{F}_p) \cup \{\mathsf{fail}\}$: $\mathrm{toPoint}(\infty) = 0$ (the Mathlib point at infinity — a genuine point, not $\mathsf{fail}$); $\mathrm{toPoint}(x, y) = (x \bmod p, y \bmod p)$ (an affine point of $W$, using the previous lemma for nonsingularity) if $\mathrm{onCurve}(x, y)$ is true; and $\mathrm{toPoint}(x, y) = \mathsf{fail}$ otherwise.

**`tp` (definition).** The total conversion $\mathrm{tp}(P) \in W(\mathbb{F}_p)$: $\mathrm{toPoint}(P)$ if that is not $\mathsf{fail}$, and $0$ otherwise. So $\mathrm{tp}(\infty) = 0$, $\mathrm{tp}(x,y) = (x \bmod p, y \bmod p)$ for on-curve pairs, and every off-curve pair is sent to $0$ (the same image as $\infty$). Pairs differing by multiples of $p$ have the same image.

**`Valid` (definition).** For an executable point $P$, $\mathrm{Valid}(P)$ is the proposition: for all naturals $x, y$, if $P = (x, y)$ then $\mathrm{onCurve}(x, y)$ is true. $\infty$ is Valid; coordinates are not required to be below $p$.

**`Reduced` (definition).** For an executable point $P$, $\mathrm{Reduced}(P)$ is the proposition: for all naturals $x, y$, if $P = (x, y)$ then $x < p$ and $y < p$. $\infty$ is Reduced; being on the curve is not required.

**`ofPoint` (definition).** Converts a Mathlib point to an executable point: $0 \mapsto \infty$ and an affine point $(x, y)$ with $x, y \in \mathbb{F}_p$ $\mapsto (\mathrm{val}(x), \mathrm{val}(y))$, where $\mathrm{val}$ is the canonical representative in $\{0, \dots, p-1\}$.

**`Gpt` (definition).** $G_{\mathrm{pt}} \in W(\mathbb{F}_p)$ is the affine point $(G_x \bmod p,\ G_y \bmod p)$; its nonsingularity is obtained from $\mathrm{onCurve}(G_x, G_y) = \text{true}$, which is checked by evaluation.

**`pneg` (definition).** Executable negation: $\mathrm{pneg}(\infty) = \infty$ and $\mathrm{pneg}(x, y) = \big(x,\ (p - y \bmod p) \bmod p\big)$; the first coordinate is kept as is (unreduced if it was), the second becomes the residue of $-y$ in $\{0, \dots, p-1\}$.

**`hasEvenY` (definition).** For a pair $(x, y)$ of naturals, $\mathrm{hasEvenY}(x, y)$ is the boolean "$y \bmod 2 = 0$", computed on the raw natural $y$ (no reduction mod $p$).

**`evenY` (definition).** For a Mathlib point: $\mathrm{evenY}(0) = \text{true}$ (infinity counts as even), and $\mathrm{evenY}(x, y)$ is the boolean "$\mathrm{val}(y)$ is even", with $\mathrm{val}(y) \in \{0, \dots, p-1\}$.

**`tagged` (definition).** $\mathrm{tagged}(s, m) = \mathrm{taggedHash}(\mathrm{ascii}(s), m) = \mathrm{SHA256}\big(\mathrm{SHA256}(\mathrm{ascii}(s)) \Vert \mathrm{SHA256}(\mathrm{ascii}(s)) \Vert m\big)$ for a text tag $s$ and a byte string $m$.

**`xbytes` (definition).** For a pair $P = (x, y)$, $\mathrm{xbytes}(P) = \mathrm{be32}(x)$, the $32$-byte big-endian encoding of $x \bmod 2^{256}$.

**`cbytes` (definition).** For a pair $P = (x, y)$, $\mathrm{cbytes}(P) = [c] \Vert \mathrm{xbytes}(P)$, a $33$-byte string whose first byte is $c = 2$ if $\mathrm{hasEvenY}(P)$ and $c = 3$ otherwise.

**`zero33` (definition).** $\mathrm{zero}_{33}$ is the byte string consisting of $33$ zero bytes.

**`cbytesExt` (definition).** For an executable point: $\mathrm{cbytesExt}(\infty) = \mathrm{zero}_{33}$ and $\mathrm{cbytesExt}(P) = \mathrm{cbytes}(P)$ for a pair $P$.

**`cpoint` (definition).** $\mathrm{cpoint}(b) = \mathrm{parsePubkey}(b)$ if $|b| = 33$, and failure otherwise. Unfolded: for $b = [t] \Vert r$ of length $33$, it fails unless $t \in \{2, 3\}$; then $x = \mathrm{beVal}(r)$, it fails if $x \ge p$, and otherwise returns $\mathrm{liftXParity}(x, \mathit{odd} = (t = 3))$ (which may fail). The result type is "optional pair of naturals", which is literally the same type as an executable point: a parse failure is the value $\infty$.

**`cpointExt` (definition).** $\mathrm{cpointExt}(b)$ is an optional executable point: if $b = \mathrm{zero}_{33}$ it succeeds with $\infty$; otherwise it succeeds with the pair $\mathrm{cpoint}(b)$ when $\mathrm{cpoint}(b)$ succeeds, and fails when $\mathrm{cpoint}(b)$ fails (here failure and $\infty$ are distinct outcomes).

**`KeyAggCtx` (record type).** A key-aggregation context is a triple $(Q, \mathit{gacc}, \mathit{tacc})$ where $Q$ is a pair of naturals (by its type it can never be $\infty$) and $\mathit{gacc}, \mathit{tacc}$ are naturals. The type is given automatically derived printing and decidable equality (componentwise).

**`hashKeys` (definition).** For a list of byte strings $pk_1, \dots, pk_u$: $\mathrm{hashKeys} = \mathrm{tagged}(\text{"KeyAgg list"},\ pk_1 \Vert pk_2 \Vert \cdots \Vert pk_u)$ (for the empty list, the tagged hash of the empty string).

**`getSecondKey` (definition).** For a list $pks$: if it is empty, $\mathrm{zero}_{33}$; otherwise, with $pk_1$ its first entry, the first entry of $pks$ (scanning from the start) that is different from $pk_1$, or $\mathrm{zero}_{33}$ if there is none.

**`keyAggCoeffInternal` (definition).** For a list $pks$ and byte strings $pk, pk_2$: the natural number $1$ if $pk = pk_2$, and otherwise $\mathrm{beVal}\big(\mathrm{tagged}(\text{"KeyAgg coefficient"},\ \mathrm{hashKeys}(pks) \Vert pk)\big) \bmod n$.

**`keyAggCoeff` (definition).** $\mathrm{keyAggCoeff}(pks, pk) = \mathrm{keyAggCoeffInternal}(pks, pk, \mathrm{getSecondKey}(pks))$: it is $1$ when $pk$ equals the second key, and the hash-derived value mod $n$ otherwise. $pk$ need not occur in $pks$.

**`keyAggSum` (definition).** For a fixed list $pks$ (used for the coefficients) and a list $\ell$ of byte strings, an optional executable point defined by recursion on $\ell$: for $\ell$ empty it succeeds with $\infty$; for $\ell = pk :: \mathit{rest}$ it succeeds with
$$\mathrm{padd}\big(\mathrm{pmul}(\mathrm{keyAggCoeff}(pks, pk),\ P),\ \mathit{acc}\big)$$
if $\mathrm{cpoint}(pk)$ succeeds with a pair $P$ and $\mathrm{keyAggSum}(pks, \mathit{rest})$ succeeds with $\mathit{acc}$, and fails otherwise. For $\ell = (pk_1, \dots, pk_u)$ with all keys parsing to $P_i$ and $a_i = \mathrm{keyAggCoeff}(pks, pk_i)$ this is the right-nested sum $\mathrm{padd}(a_1P_1, \mathrm{padd}(a_2P_2, \dots, \mathrm{padd}(a_uP_u, \infty)\cdots))$, with $a_iP_i = \mathrm{pmul}(a_i, P_i)$.

**`keyAgg` (definition).** $\mathrm{keyAgg}(pks)$: compute $\mathrm{keyAggSum}(pks, pks)$; if it succeeds with a pair $Q$, the result is the context $(Q, \mathit{gacc} = 1, \mathit{tacc} = 0)$; if it fails (some key does not parse) or yields $\infty$, $\mathrm{keyAgg}$ fails. For the empty list the sum is $\infty$, so $\mathrm{keyAgg}$ fails.

**`applyTweak` (definition).** For a context $(Q, \mathit{gacc}, \mathit{tacc})$, a byte string $\mathit{tweak}$ and a boolean $\mathit{isXonly}$:

1. $g = n - 1$ if $\mathit{isXonly}$ is true and $\mathrm{hasEvenY}(Q)$ is false; otherwise $g = 1$.
2. $t = \mathrm{beVal}(\mathit{tweak})$ (the length of $\mathit{tweak}$ is not checked).
3. If $t \ge n$, fail.
4. $Q' = \mathrm{padd}\big(\mathrm{pmul}(g, Q),\ \mathrm{pmul}(t, G)\big)$; if $Q' = \infty$, fail.
5. Otherwise succeed with $\big(Q',\ (g\cdot\mathit{gacc}) \bmod n,\ (t + g\cdot\mathit{tacc}) \bmod n\big)$.

**`applyTweaks` (definition).** For a context and a list of (tweak, flag) pairs: with the empty list, succeed with the context unchanged; otherwise apply $\mathrm{applyTweak}$ with the first pair, fail if it fails, and continue with the remaining pairs from the new context.

**`keyAggTweaked` (definition).** $\mathrm{keyAggTweaked}(pks, \mathit{tweaks})$: fail if $\mathrm{keyAgg}(pks)$ fails; otherwise $\mathrm{applyTweaks}$ of its context with $\mathit{tweaks}$.

**`nonceSum` (definition).** For $j \in \mathbb{N}$ and a list $\ell$ of byte strings, an optional executable point by recursion on $\ell$: for $\ell$ empty it succeeds with $\infty$; for $\ell = pn :: \mathit{rest}$ it succeeds with $\mathrm{padd}(R, \mathit{acc})$ if $\mathrm{cpoint}\big(\mathrm{take}_{33}(\mathrm{drop}_{33j}(pn))\big)$ succeeds with a pair $R$ and $\mathrm{nonceSum}(j, \mathit{rest})$ succeeds with $\mathit{acc}$, and fails otherwise. Each individual slice must parse as a genuine pair (it cannot be $\infty$; $\mathrm{zero}_{33}$ does not parse). The total length of $pn$ is not checked: for $j = 0$ its first $33$ bytes are used, for $j = 1$ its bytes $33$ to $65$, other bytes are ignored.

**`nonceAgg` (definition).** For a list of public nonces: if $\mathrm{nonceSum}(0, \cdot)$ succeeds with $R_1$ and $\mathrm{nonceSum}(1, \cdot)$ succeeds with $R_2$, the result is the $66$-byte string $\mathrm{cbytesExt}(R_1) \Vert \mathrm{cbytesExt}(R_2)$; otherwise it fails. For the empty list the result is $\mathrm{zero}_{33} \Vert \mathrm{zero}_{33}$.

**`SessionCtx` (record type).** A session context consists of a byte string $\mathit{aggnonce}$, a list of byte strings $pks$, a list $\mathit{tweaks}$ of pairs (byte string, boolean), and a byte string $\mathit{msg}$, with no constraints among them.

**`SessionValues` (record type).** A record $(Q, \mathit{gacc}, \mathit{tacc}, b, R', R, e)$ with $Q$ and $R$ pairs of naturals, $\mathit{gacc}, \mathit{tacc}, b, e$ naturals, and $R'$ an executable point (possibly $\infty$).

**`getSessionValues` (definition).** For a session context $(\mathit{aggnonce}, pks, \mathit{tweaks}, \mathit{msg})$, an optional session-values record:

1. If $\mathrm{keyAggTweaked}(pks, \mathit{tweaks})$ fails, fail; otherwise let $(Q, \mathit{gacc}, \mathit{tacc})$ be its result.
2. $b = \mathrm{beVal}\big(\mathrm{tagged}(\text{"MuSig/noncecoef"},\ \mathit{aggnonce} \Vert \mathrm{xbytes}(Q) \Vert \mathit{msg})\big) \bmod n$, hashing the whole $\mathit{aggnonce}$ whatever its length.
3. $R_1 = \mathrm{cpointExt}(\mathrm{take}_{33}(\mathit{aggnonce}))$ and $R_2 = \mathrm{cpointExt}(\mathrm{take}_{33}(\mathrm{drop}_{33}(\mathit{aggnonce})))$; if either fails, fail. Each is $\infty$ (slice equal to $\mathrm{zero}_{33}$) or a parsed pair.
4. $R' = \mathrm{padd}\big(R_1, \mathrm{pmul}(b, R_2)\big)$.
5. $R = (G_x, G_y)$ if $R' = \infty$, and $R = R'$ otherwise.
6. $e = \mathrm{beVal}\big(\mathrm{tagged}(\text{"BIP0340/challenge"},\ \mathrm{xbytes}(R) \Vert \mathrm{xbytes}(Q) \Vert \mathit{msg})\big) \bmod n$.
7. Succeed with $(Q, \mathit{gacc}, \mathit{tacc}, b, R', R, e)$.

**`partialSigVerifyInternal` (definition).** For byte strings $\mathit{psig}$, $\mathit{pubnonce}$, $pk$ and a session context $ctx$, a boolean:

1. If $\mathrm{getSessionValues}(ctx)$ fails, false; otherwise use its $(Q, \mathit{gacc}, \mathit{tacc}, b, R', R, e)$.
2. $s = \mathrm{beVal}(\mathit{psig})$; if $|\mathit{psig}| \neq 32$ or $s \ge n$, false.
3. $R_1 = \mathrm{cpoint}(\mathrm{take}_{33}(\mathit{pubnonce}))$, $R_2 = \mathrm{cpoint}(\mathrm{take}_{33}(\mathrm{drop}_{33}(\mathit{pubnonce})))$, $P = \mathrm{cpoint}(pk)$; if any of them fails, false.
4. If $pk$ is not an entry of $ctx$'s key list $pks$, false.
5. $R_e' = \mathrm{padd}\big(R_1, \mathrm{pmul}(b, R_2)\big)$; $R_e = R_e'$ if $\mathrm{hasEvenY}(R)$, otherwise $R_e = \mathrm{pneg}(R_e')$.
6. $a = \mathrm{keyAggCoeff}(pks, pk)$; $g = 1$ if $\mathrm{hasEvenY}(Q)$, otherwise $g = n - 1$; $g' = (g\cdot\mathit{gacc}) \bmod n$.
7. The result is true iff the executable points $\mathrm{pmul}(s, G)$ and $\mathrm{padd}\big(R_e,\ \mathrm{pmul}((e\cdot a\cdot g') \bmod n,\ P)\big)$ are literally equal (both $\infty$ or the same pair of naturals).

**`partialSigAgg` (definition).** For a list of byte strings $\mathit{psig}_1, \dots, \mathit{psig}_u$ and a session context, an optional byte string:

1. If $\mathrm{getSessionValues}(ctx)$ fails, fail; otherwise use its values.
2. If some $\mathit{psig}_i$ has $|\mathit{psig}_i| \neq 32$ or $\mathrm{beVal}(\mathit{psig}_i) \ge n$, fail.
3. $g = 1$ if $\mathrm{hasEvenY}(Q)$, otherwise $g = n - 1$.
4. $s = \big(\sum_{i=1}^{u} \mathrm{beVal}(\mathit{psig}_i) + e\cdot g\cdot\mathit{tacc}\big) \bmod n$ (natural arithmetic; the empty sum is $0$, so for $u = 0$, $s = (e\,g\,\mathit{tacc}) \bmod n$).
5. Succeed with the $64$-byte string $\mathrm{xbytes}(R) \Vert \mathrm{be32}(s)$.

**`lagrangeCoeff` (definition).** For a finite set $S$ of natural numbers and a natural $i$, the element of $\mathbb{Z}/n\mathbb{Z}$
$$\lambda_i^S = \prod_{j \in S \setminus \{i\}} (j : \mathbb{Z}/n)\cdot\big((j : \mathbb{Z}/n) - (i : \mathbb{Z}/n)\big)^{-1},$$
where $(j : \mathbb{Z}/n)$ is the residue $j \bmod n$, subtraction is in $\mathbb{Z}/n$, and ${}^{-1}$ is Mathlib's total inverse on $\mathbb{Z}/n$ (the multiplicative inverse for residues coprime to $n$, and $0^{-1} = 0$; the file registers no primality instance for $n$). The empty product is $1$ (e.g. for $S = \{i\}$ or $S = \emptyset$); if $i \notin S$ nothing is removed from $S$; a factor with $j \equiv i \pmod n$, $j \neq i$, equals $j\cdot 0^{-1} = 0$.
