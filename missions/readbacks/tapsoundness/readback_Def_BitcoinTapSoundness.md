# Read-back: `Def_BitcoinTapSoundness.lean`

Throughout, a *byte* is an 8-bit value, $\mathsf{Bytes}$ is the set of finite byte strings (any length, including empty), $\|$ is concatenation, $\mathrm{SHA256}$ is the bundle's own executable SHA-256 (a total function from $\mathsf{Bytes}$ to 32-byte strings), $\mathrm{utf8}(\cdot)$ is UTF-8 encoding of a string, and $\mathrm{Tagged}_{\tau}(m) := \mathrm{SHA256}(\mathrm{SHA256}(\mathrm{utf8}(\tau)) \| \mathrm{SHA256}(\mathrm{utf8}(\tau)) \| m)$. $\mathrm{CS}(\ell)$ is the compact-size encoding of $\ell$ (one byte if $\ell < 253$; $0xfd$ + 2 little-endian bytes if $\ell \le 65535$; $0xfe$ + 4 bytes if $\ell \le 2^{32}-1$; $0xff$ + 8 bytes of $\ell \bmod 2^{64}$ otherwise). $\mathrm{LeafHash}(v,s) := \mathrm{Tagged}_{\text{``TapLeaf''}}([v] \| \mathrm{CS}(|s|) \| s)$ with the byte $v$ used as given. $\prec$ is lexicographic order on byte strings (first differing byte decides by numeric value; a proper prefix is smaller; no string is $\prec$ itself) and $\mathrm{BranchHash}(a,b) := \mathrm{Tagged}_{\text{``TapBranch''}}(\text{if } a \prec b \text{ then } a\|b \text{ else } b\|a)$, which is symmetric.

## `Sha256Collision`

A closed proposition (no parameters):
$$
\mathsf{Sha256Collision} \;:=\; \exists\, x, y \in \mathsf{Bytes}.\; x \neq y \;\wedge\; \mathrm{SHA256}(x) = \mathrm{SHA256}(y).
$$
The two strings may have any lengths (not necessarily equal); "$x \neq y$" is inequality of byte strings. Because $\mathrm{SHA256}$ here is a specific total function from the infinite set $\mathsf{Bytes}$ to the finite set of 32-byte strings, this proposition's truth value is a fixed mathematical fact (by counting, such a pair exists); it is a definition, not an axiom or assumption, and nothing in the file postulates it to be false.

## `TapTree`

An inductively defined type of finite binary trees: a tap tree is either a **leaf** carrying a byte $v$ (the "version") and a byte string $s$ (the "script", any length), or a **branch** with exactly two ordered subtrees $L$ and $R$ (both tap trees). There are no other constructors; every internal node has exactly two children; a single leaf is a tap tree. No constraint is placed on $v$ or $s$.

## `TapTree.hash`

The hash of a tap tree, a 32-byte string, defined by recursion:
$$
\mathrm{hash}(\mathrm{leaf}(v,s)) := \mathrm{LeafHash}(v,s), \qquad
\mathrm{hash}(\mathrm{branch}(L,R)) := \mathrm{BranchHash}(\mathrm{hash}(L), \mathrm{hash}(R)).
$$
Since $\mathrm{BranchHash}$ orders its two inputs lexicographically before hashing, $\mathrm{hash}(\mathrm{branch}(L,R)) = \mathrm{hash}(\mathrm{branch}(R,L))$.

## `TapTree.leaves`

The list of leaf hashes of a tap tree, defined by recursion:
$$
\mathrm{leaves}(\mathrm{leaf}(v,s)) := [\mathrm{LeafHash}(v,s)], \qquad
\mathrm{leaves}(\mathrm{branch}(L,R)) := \mathrm{leaves}(L) \,\|\, \mathrm{leaves}(R).
$$
It lists 32-byte hashes (not the pairs $(v,s)$), left to right, keeping repetitions. It is never empty.

## `TapTree.subtreesAt`

The list of subtrees of a tap tree $T$ at depth $d$, defined by recursion on $T$ and $d$:
$$
\mathrm{subtreesAt}(T, 0) := [T] \ \text{(for any } T\text{)},\qquad
\mathrm{subtreesAt}(\mathrm{leaf}(v,s), d+1) := [\,],\qquad
\mathrm{subtreesAt}(\mathrm{branch}(L,R), d+1) := \mathrm{subtreesAt}(L,d) \,\|\, \mathrm{subtreesAt}(R,d).
$$
So it lists, left to right, exactly the subtrees whose root is at depth $d$ below the root of $T$; it is empty when $d$ is larger than the depth of every node reached (e.g. a single leaf at any $d \ge 1$).

## `TweakCollision`

For a byte string $q$, a Boolean $\pi$ and a point $P = (P_x, P_y)$ (a pair of natural numbers, not required to lie on the curve or be reduced mod $p$):
$$
\mathrm{TweakCollision}(q, \pi, P) := \exists\, t_1, t_2 \in \mathsf{Bytes}.\; t_1 \neq t_2 \;\wedge\; \mathrm{TweakCheck}(q,\pi,P,t_1) = \mathrm{true} \;\wedge\; \mathrm{TweakCheck}(q,\pi,P,t_2) = \mathrm{true},
$$
where $\mathrm{TweakCheck}(q,\pi,P,t)$ is: let $\hat t := \mathrm{be}(t)$ be the big-endian value of $t$ (any length; empty $\mapsto 0$; leading zero bytes do not change it); if $\hat t \ge n$ (with $n$ the fixed secp256k1 group-order constant), the result is false; otherwise let $Q := P \oplus (\hat t \cdot G)$, using the file's affine addition formulas modulo $p = 2^{256} - 2^{32} - 977$ (identity $\infty$; doubling when the abscissas agree mod $p$ and the ordinates do not sum to $0$ mod $p$, else $\infty$; chord formula otherwise; Fermat inversion with $0^{-1} := 0$) and double-and-add scalar multiplication with 257 steps ($0 \cdot G = \infty$) from the fixed base point $G$; if $Q = \infty$, false; otherwise true exactly when the 32-byte big-endian encoding of $Q_x \bmod 2^{256}$ equals $q$ as a byte string (so $q$ must have length 32) and ($Q_y$ odd) $\Leftrightarrow$ $\pi$. The witnesses $t_1, t_2$ are required to differ only as byte strings; no length (such as 32) is imposed on them, and since the check reads them only through $\mathrm{be}(\cdot)$, if some $t$ passes the check then $t$ and $0x00 \| t$ are two distinct witnesses. Hence $\mathrm{TweakCollision}(q,\pi,P)$ holds exactly when at least one byte string passes $\mathrm{TweakCheck}(q,\pi,P,\cdot)$.

## `HonestOutput`

For byte strings $q$, $K$, a Boolean $\pi$ and a tap tree $T$:
$$
\mathrm{HonestOutput}(q, K, \pi, T) := \bigl[\mathrm{CheckTapTweak}(q, K, \mathrm{hash}(T), \pi) = \mathrm{true}\bigr],
$$
where $\mathrm{CheckTapTweak}(q,K,r,\pi)$ is: compute $\mathrm{liftX}(\mathrm{be}(K))$ — undefined if $\mathrm{be}(K) \ge p$; otherwise with $x := \mathrm{be}(K)$ and $y_0 := (x^3+7)^{(p+1)/4} \bmod p$, if $y_0^2 \equiv x^3 + 7 \pmod p$ it is the point $(x, y)$ with $y = y_0$ if $y_0$ is even and $y = (p - y_0) \bmod p$ otherwise, and undefined if not. If undefined, $\mathrm{CheckTapTweak}$ is false. Otherwise, with $P$ that point, it is $\mathrm{TweakCheck}\bigl(q, \pi, P, \mathrm{Tagged}_{\text{``TapTweak''}}(K \| r)\bigr)$ as defined above. No length is imposed on $K$ or $q$ by the definition itself; the check can only succeed if $q$ is exactly 32 bytes, and $K$ enters only through its big-endian value (any length) and through its raw bytes inside the tweak hash input.

## `controlInternalKey`

For a byte string $c$: $\mathrm{controlInternalKey}(c) := (\text{drop the first byte of } c)\text{, then take the first 32 bytes}$. If $|c| \ge 33$ this is exactly the bytes at zero-based positions $1$ through $32$; if $1 \le |c| < 33$ it is the $|c| - 1$ bytes after the first; if $c$ is empty it is the empty string.

## `controlParity`

For a byte string $c$: $\mathrm{controlParity}(c) := \mathrm{true}$ if the numeric value of the first byte of $c$ is odd, and $\mathrm{false}$ otherwise; if $c$ is empty the first byte defaults to $0$, so the result is $\mathrm{false}$.
