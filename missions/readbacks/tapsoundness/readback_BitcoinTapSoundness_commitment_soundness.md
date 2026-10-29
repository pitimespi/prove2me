# Read-back: `BitcoinTapSoundness.commitment_soundness`

**Statement.** Let $q$ and $K$ ("`internal32`") be byte strings (finite sequences of 8-bit values; **no length hypothesis is stated for either**), $\pi$ ("`parity`") a Boolean, and $T$ a tap tree (a finite binary tree in which every internal node has exactly two ordered children and every leaf carries a byte and a byte string). Let $c$ ("`control`") be a byte string and $k$ a natural number (possibly $0$). Let $v$ be a byte and $s$ a byte string (any length). Assume all of the following:

- **(hT)** $\mathrm{HonestOutput}(q, K, \pi, T)$, i.e. $\mathrm{CheckTapTweak}\bigl(q, K, \mathrm{hash}(T), \pi\bigr) = \mathrm{true}$;
- **(hc)** $|c| = 33 + 32\,k$;
- **(hkey)** the 32 bytes of $c$ at positions $1$ through $32$ (zero-based; i.e. drop the first byte, then take 32) equal $K$ as byte strings — so under (hc), $|K| = 32$;
- **(hpar)** $\pi = \mathrm{true}$ exactly when the first byte of $c$ is odd (i.e. $c_0 \bmod 2 = 1$; if $c$ were empty the first byte would default to $0$, but (hc) rules this out);
- **(h)** $\mathrm{VerifyCommit}\bigl(c, q, \mathrm{LeafHash}(v, s)\bigr) = \mathrm{true}$.

Then at least one of the following three holds:

1. $\mathrm{LeafHash}(v, s)$ is an element of the list $\mathrm{leaves}(T)$ of leaf hashes of $T$; or
2. $\mathsf{Sha256Collision}$: there exist byte strings $x \neq y$ (any lengths, unrelated to the theorem's variables) with $\mathrm{SHA256}(x) = \mathrm{SHA256}(y)$; or
3. there exists a point $P = (P_x, P_y)$ (a pair of natural numbers) such that $\mathrm{liftX}(\mathrm{be}(K)) = P$ (the lift succeeds and yields $P$) **and** $\mathrm{TweakCollision}(q, \pi, P)$ holds, i.e. there exist byte strings $t_1 \neq t_2$ with $\mathrm{TweakCheck}(q, \pi, P, t_1) = \mathrm{true}$ and $\mathrm{TweakCheck}(q, \pi, P, t_2) = \mathrm{true}$.

**Unfolded notions (hashing).**

- $\mathrm{SHA256}$ is the bundle's own executable implementation of SHA-256, a total function from all finite byte strings to 32-byte strings. $\mathrm{utf8}(\cdot)$ is UTF-8 encoding, and for a tag string $\tau$,
$$
\mathrm{Tagged}_{\tau}(m) := \mathrm{SHA256}\bigl(\mathrm{SHA256}(\mathrm{utf8}(\tau)) \| \mathrm{SHA256}(\mathrm{utf8}(\tau)) \| m\bigr).
$$
- $\mathrm{CS}(\ell)$ is the compact-size encoding of $\ell$ (one byte if $\ell < 253$; $0xfd$ + 2 little-endian bytes if $\ell \le 65535$; $0xfe$ + 4 bytes if $\ell \le 2^{32}-1$; $0xff$ + 8 bytes of $\ell \bmod 2^{64}$ otherwise).
- $\mathrm{LeafHash}(v, s) := \mathrm{Tagged}_{\text{``TapLeaf''}}([v] \| \mathrm{CS}(|s|) \| s)$ ($v$ used as given, no masking).
- $\prec$ is lexicographic order on byte strings (first differing byte decides; a proper prefix is smaller; no string is $\prec$ itself) and $\mathrm{BranchHash}(a, b) := \mathrm{Tagged}_{\text{``TapBranch''}}(\text{if } a \prec b \text{ then } a\|b \text{ else } b\|a)$ (symmetric in $a,b$).
- $\mathrm{hash}(\mathrm{leaf}(v,s)) := \mathrm{LeafHash}(v,s)$; $\mathrm{hash}(\mathrm{branch}(L,R)) := \mathrm{BranchHash}(\mathrm{hash}(L), \mathrm{hash}(R))$. $\mathrm{leaves}(\mathrm{leaf}(v,s)) := [\mathrm{LeafHash}(v,s)]$; $\mathrm{leaves}(\mathrm{branch}(L,R)) := \mathrm{leaves}(L)\|\mathrm{leaves}(R)$ (leaf hashes left to right, with repetitions). Disjunct (1) is membership of a 32-byte string in this list, not an assertion that the pair $(v,s)$ occurs in $T$.
- Path nodes of $c$: with $m := \lfloor(|c| \mathbin{\dot-} 33)/32\rfloor$ ($\dot-$ truncated subtraction), drop the first 33 bytes of $c$ and cut the rest into $m$ consecutive 32-byte blocks $[n_1,\dots,n_m]$, ignoring any leftover. Under (hc), $m = k$ exactly. The Merkle root from $c$ and a start hash $h$ is the left fold $\mathrm{Root}(c,h) := \mathrm{BranchHash}(\cdots\mathrm{BranchHash}(\mathrm{BranchHash}(h,n_1),n_2)\cdots,n_m)$, equal to $h$ when $m = 0$.
- $\mathrm{TweakHash}(K, r) := \mathrm{Tagged}_{\text{``TapTweak''}}(K \| r)$.

**Unfolded notions (curve arithmetic).**

- $p := 2^{256} - 2^{32} - 977$; $n := \mathtt{0xFFFFFFFF\,FFFFFFFF\,FFFFFFFF\,FFFFFFFE\,BAAEDCE6\,AF48A03B\,BFD25E8C\,D0364141}$; $G := (G_x, G_y)$ is the fixed secp256k1 base point given by two 256-bit constants.
- $\mathrm{be}(b)$ is the big-endian natural-number value of a byte string $b$ of any length ($\mathrm{be}([]) = 0$; leading zero bytes do not change the value). $\mathrm{be}_{32}(x)$ is the 32-byte big-endian encoding of $x \bmod 2^{256}$.
- Points are either $\infty$ or pairs of natural numbers (not required to be reduced mod $p$ or to lie on the curve). Addition $\oplus$: $\infty$ is the identity; for $(x_1,y_1) \oplus (x_2,y_2)$, if $x_1 \equiv x_2 \pmod p$ then the result is $\infty$ when $y_1 + y_2 \equiv 0 \pmod p$ and otherwise the doubling formula with slope $\lambda = 3x_1^2 \cdot (2y_1)^{-1} \bmod p$; otherwise the chord formula with slope $\lambda = (y_2 - y_1)(x_2 - x_1)^{-1} \bmod p$; in both cases $x_3 = \lambda^2 - x_1 - x_2 \bmod p$ and $y_3 = \lambda(x_1 - x_3) - y_1 \bmod p$. Inverses are computed by Fermat exponentiation, with the "inverse" of $0$ being $0$. Scalar multiplication $t \cdot P$ is double-and-add on the binary digits of $t$ with a fuel of 257 steps (exact for $t < 2^{257}$), with $0 \cdot P = \infty$.
- $\mathrm{liftX}(x)$: if $x \ge p$, undefined (none). Otherwise let $y_0 := (x^3 + 7)^{(p+1)/4} \bmod p$; if $y_0^2 \equiv x^3 + 7 \pmod p$, the result is $(x, y)$ with $y = y_0$ if $y_0$ is even and $y = (p - y_0) \bmod p$ otherwise (the even-$y$ point with abscissa $x$); if not, undefined.
- $\mathrm{TweakCheck}(q, \pi, P, t)$ for byte strings $q, t$ (any lengths), Boolean $\pi$, and point $P$: let $\hat t := \mathrm{be}(t)$. If $\hat t \ge n$, false. Otherwise compute $Q := P \oplus (\hat t \cdot G)$. If $Q = \infty$, false. Otherwise true exactly when $\mathrm{be}_{32}(Q_x) = q$ as byte strings (so $q$ must be exactly 32 bytes) **and** ($Q_y$ is odd) $\Leftrightarrow$ $\pi$.
- $\mathrm{CheckTapTweak}(q, K, r, \pi)$: if $\mathrm{liftX}(\mathrm{be}(K))$ is undefined, false; otherwise, with $P$ its value, $\mathrm{TweakCheck}\bigl(q, \pi, P, \mathrm{TweakHash}(K, r)\bigr)$.
- $\mathrm{VerifyCommit}(c, q, h) := \mathrm{CheckTapTweak}\bigl(q,\ c[1..32],\ \mathrm{Root}(c, h),\ [c_0 \text{ odd}]\bigr)$, where $c[1..32]$ is "drop one byte, take 32" (shorter if $c$ is short) and $c_0$ is the first byte of $c$ (default $0$ if empty). Under (hkey) and (hpar) this is $\mathrm{CheckTapTweak}(q, K, \mathrm{Root}(c, \mathrm{LeafHash}(v,s)), \pi)$.
- $\mathrm{TweakCollision}(q, \pi, P) := \exists\, t_1, t_2 \in \mathsf{Bytes}.\; t_1 \neq t_2 \wedge \mathrm{TweakCheck}(q,\pi,P,t_1) = \mathrm{true} \wedge \mathrm{TweakCheck}(q,\pi,P,t_2) = \mathrm{true}$. The inequality $t_1 \neq t_2$ is inequality of byte strings; no length is imposed on $t_1, t_2$, and the check reads them only through $\mathrm{be}(\cdot)$, which ignores leading zero bytes. Consequently, whenever some $t$ passes the check, the strings $t$ and $0x00 \| t$ are two distinct witnesses; in particular, under (h), (hkey), (hpar), the tweak $\mathrm{TweakHash}(K, \mathrm{Root}(c, \mathrm{LeafHash}(v,s)))$ passes the check for the point $P = \mathrm{liftX}(\mathrm{be}(K))$.
- $\mathsf{Sha256Collision}$ is the closed proposition $\exists\, x, y \in \mathsf{Bytes}.\; x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$; since it concerns a fixed total function from infinitely many inputs to finitely many 32-byte outputs, its truth value is a fixed mathematical fact (such a pair exists by counting), not an assumption.

**Edge cases made explicit.** Hypotheses (hT) and (h) can only be true when $q$ is exactly 32 bytes and $\mathrm{be}(K) < p$ with $\mathrm{liftX}$ succeeding; otherwise the theorem's hypotheses are unsatisfiable and it holds vacuously. $k = 0$ is allowed (no path nodes; root $= \mathrm{LeafHash}(v,s)$); no upper bound on $k$ is imposed. Under (hT), the same point $P = \mathrm{liftX}(\mathrm{be}(K))$ is used with tweak $\mathrm{TweakHash}(K, \mathrm{hash}(T))$; under (h), with tweak $\mathrm{TweakHash}(K, \mathrm{Root}(c, \mathrm{LeafHash}(v,s)))$. The conclusion's disjunct (3) quantifies over $P$ but fixes it to be the value of $\mathrm{liftX}(\mathrm{be}(K))$.
