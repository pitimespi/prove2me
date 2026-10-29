# Read-back: `Def_BitcoinTapSoundnessV2.lean`

Conventions used throughout this read-back. A *byte* is an 8-bit vector; a *byte string* is a finite list of bytes (possibly empty); $\|$ is concatenation of byte strings; $|x|$ is the length of $x$. $\mathrm{SHA256}$ denotes the bundle's own executable function `sha256`: a total function from byte strings to byte strings that appends the byte $\mathtt{0x80}$, then zero bytes until the length is $\equiv 56 \pmod{64}$, then the bit-length of the original message as 8 big-endian bytes; splits the padded string into 64-byte chunks; folds the SHA-256 compression function over the chunks from the standard initial state; and emits the eight 32-bit state words as big-endian 4-byte groups (a 32-byte string). It is defined on every byte string. $\mathrm{ascii}(t)$ is the list of UTF-8 code units of the string $t$, each taken as one byte. The preamble's $\mathrm{tagged}(t, m)$ is $\mathrm{SHA256}\big(\mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, m\big)$.

The file declares the following, in order.

---

## 1. `Collides`

For byte strings $x$ and $y$, $\mathrm{Collides}(x, y)$ is the proposition

$$x \neq y \;\wedge\; \mathrm{SHA256}(x) = \mathrm{SHA256}(y).$$

It requires both conjuncts: the two strings must be *different* byte strings (as lists, so differing in length or in some byte) *and* have identical 32-byte SHA-256 output. No length constraint is placed on $x$ or $y$; either may be empty. Note that $\mathrm{Collides}(x, x)$ is false for every $x$.

## 2. `taggedPre`

For a string $t$ and a byte string $m$,

$$\mathrm{taggedPre}(t, m) \;=\; \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, m,$$

a byte string of length $64 + |m|$. This is exactly the string whose SHA-256 the preamble's $\mathrm{tagged}(t,m)$ computes, i.e. $\mathrm{tagged}(t, m) = \mathrm{SHA256}(\mathrm{taggedPre}(t, m))$ by unfolding (the file states this as a comment; the equation itself is a separate theorem).

## 3. `leafMsg`

For a byte $v$ and a byte string $s$,

$$\mathrm{leafMsg}(v, s) \;=\; [v] \,\|\, \mathrm{writeCompactSize}(|s|) \,\|\, s,$$

where $\mathrm{writeCompactSize}(n)$ is the preamble's Bitcoin compact-size encoding of the natural number $n$: if $n < 253$, the single byte $n$; else if $n \le \mathtt{0xffff}$, the byte $253$ followed by the 2 little-endian bytes of $n$; else if $n \le \mathtt{0xffffffff}$, the byte $254$ followed by the 4 little-endian bytes of $n$; otherwise the byte $255$ followed by the 8 little-endian bytes of $n$ (reduced modulo $2^{64}$). The preamble's $\mathrm{tapleafHash}(v, s)$ is $\mathrm{tagged}(\text{"TapLeaf"}, [v] \| \mathrm{writeCompactSize}(|s|) \| s)$, i.e. $\mathrm{tagged}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s))$ by unfolding. No constraint is placed on $v$ (any of the 256 byte values) or on $|s|$.

## 4. `branchMsg`

For byte strings $a$ and $b$,

$$\mathrm{branchMsg}(a, b) \;=\; \begin{cases} a \,\|\, b & \text{if } \mathrm{lexLt}(a, b) \\ b \,\|\, a & \text{otherwise,} \end{cases}$$

where $\mathrm{lexLt}$ is the preamble's Boolean strict lexicographic comparison on byte strings, defined recursively: $\mathrm{lexLt}([], []) = \mathrm{false}$; $\mathrm{lexLt}([], b{::}bs) = \mathrm{true}$; $\mathrm{lexLt}(a{::}as, []) = \mathrm{false}$; and $\mathrm{lexLt}(a{::}as, b{::}bs)$ is true if the byte value of $a$ is less than that of $b$, false if the byte value of $b$ is less than that of $a$, and otherwise equals $\mathrm{lexLt}(as, bs)$. Thus a proper prefix is less than the longer string, and $\mathrm{lexLt}(x, x)$ is false for all $x$, so $\mathrm{branchMsg}(x, x) = x \| x$. The preamble's $\mathrm{tapbranchHash}(a, b)$ is $\mathrm{tagged}(\text{"TapBranch"}, \text{if } \mathrm{lexLt}(a,b) \text{ then } a\|b \text{ else } b\|a)$, i.e. $\mathrm{tagged}(\text{"TapBranch"}, \mathrm{branchMsg}(a,b))$ by unfolding. No length constraint is placed on $a$ or $b$.

## 5. `TapTree`

An inductive type with two constructors: $\mathrm{leaf}(v, s)$ for a byte $v$ ("version") and a byte string $s$ ("script"); and $\mathrm{branch}(l, r)$ for two trees $l$ and $r$. Every tree is finite, and every tree has at least one leaf. Equality of trees is decidable and the type has a printer; nothing else (no ordering, no balance, no depth bound, no constraint on $v$ or $s$) is imposed.

## 6. `TapTree.hash`

The hash of a tree, a byte string, by structural recursion:

$$\mathrm{hash}(\mathrm{leaf}(v, s)) = \mathrm{tapleafHash}(v, s), \qquad \mathrm{hash}(\mathrm{branch}(l, r)) = \mathrm{tapbranchHash}(\mathrm{hash}(l), \mathrm{hash}(r)),$$

with $\mathrm{tapleafHash}$ and $\mathrm{tapbranchHash}$ as unfolded above. Since $\mathrm{tapbranchHash}$ orders its two arguments lexicographically, $\mathrm{hash}(\mathrm{branch}(l, r)) = \mathrm{hash}(\mathrm{branch}(r, l))$ by unfolding.

## 7. `TapTree.leaves`

The list of leaf hashes of a tree, by structural recursion:

$$\mathrm{leaves}(\mathrm{leaf}(v, s)) = [\mathrm{tapleafHash}(v, s)], \qquad \mathrm{leaves}(\mathrm{branch}(l, r)) = \mathrm{leaves}(l) \,\|\, \mathrm{leaves}(r).$$

It is a list of hashes (32-byte strings), not of $(v, s)$ pairs; two distinct leaves with the same hash appear twice. Membership $h \in \mathrm{leaves}(T)$ means $h$ equals some element of that list.

## 8. `TapTree.subtreesAt`

The list of subtrees of $T$ at depth $d$, a list of trees, by recursion on $T$ and $d$:

- $\mathrm{subtreesAt}(T, 0) = [T]$ for every tree $T$;
- $\mathrm{subtreesAt}(\mathrm{leaf}(v, s), d+1) = []$ (the empty list);
- $\mathrm{subtreesAt}(\mathrm{branch}(l, r), d+1) = \mathrm{subtreesAt}(l, d) \,\|\, \mathrm{subtreesAt}(r, d)$.

So for $d$ greater than the depth of every node of $T$ the result is empty, and for a tree whose leaves sit at different depths, $\mathrm{subtreesAt}(T, d)$ lists only the nodes exactly at depth $d$ (leaves above depth $d$ contribute nothing).

## 9. `walk`

A function taking a tree $T$, a list of byte strings $\mathit{path}$ ("Merkle path nodes"), and a byte string $h$, and returning *either* a tree (left result, written $\mathrm{inl}(U)$) *or* a pair of byte strings (right result, written $\mathrm{inr}(x, y)$). It is defined by recursion on the path, case by case:

- **Empty path.** $\mathrm{walk}(T, [], h) = \mathrm{inl}(T)$, for every $T$ and every $h$. No comparison between $h$ and $\mathrm{hash}(T)$ is made.

- **Non-empty path $n :: \mathit{rest}$.** First compute the recursive result $R = \mathrm{walk}(T, \mathit{rest}, \mathrm{tapbranchHash}(h, n))$, i.e. the walk on the *shorter* path with the hash replaced by the branch hash of $h$ and $n$. Then:
  - if $R = \mathrm{inr}(c)$ for some pair $c$, the result is $\mathrm{inr}(c)$ (the pair is passed up unchanged);
  - if $R = \mathrm{inl}(\mathrm{leaf}(v, s))$, the result is
    $$\mathrm{inr}\big(\mathrm{taggedPre}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s)),\; \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(h, n))\big),$$
    regardless of whether $h$ or any hash matches anything; this is the case where the walk reached a leaf while path nodes remained;
  - if $R = \mathrm{inl}(\mathrm{branch}(l, r))$, then: if $h = \mathrm{hash}(l)$ the result is $\mathrm{inl}(l)$; otherwise, if $h = \mathrm{hash}(r)$ the result is $\mathrm{inl}(r)$; otherwise the result is
    $$\mathrm{inr}\big(\mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(\mathrm{hash}(l), \mathrm{hash}(r))),\; \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(h, n))\big).$$
    When $h$ equals both children's hashes, the left child $l$ is chosen.

Unwinding the recursion for a path $[n_1, \dots, n_k]$: writing $h_0 = h$ and $h_i = \mathrm{tapbranchHash}(h_{i-1}, n_i)$, the innermost call is $\mathrm{walk}(T, [], h_k) = \mathrm{inl}(T)$; then, going outward, the step for $n_k$ compares $h_{k-1}$ against the children of $T$, the step for $n_{k-1}$ compares $h_{k-2}$ against the children of the chosen child, and so on down to the step for $n_1$, which compares $h_0 = h$ against the children of the node reached. Thus the path is listed leaf-end first and the tree is descended from the root. The function never checks that $h_k = \mathrm{hash}(T)$, never checks any lengths, and never checks that a returned pair actually collides: the pair is simply the two $\mathrm{taggedPre}$ strings written above. If the path is longer than the depth at which a leaf is reached, the leaf case fires and the remaining path nodes are not inspected (except that they have already been folded into the $h_i$). Each returned pair is an explicit expression in $T$, the path nodes and $h$.

## 10. `scriptPathWitness`

For a tree $T$, a byte string $\mathit{control}$, a byte $v$ and a byte string $s$, an optional pair of byte strings, defined by cases on

$$W = \mathrm{walk}\big(T,\; \mathrm{controlNodes}(\mathit{control}),\; \mathrm{tapleafHash}(v, s)\big):$$

- if $W = \mathrm{inr}(c)$, the result is $\mathrm{some}(c)$;
- if $W = \mathrm{inl}(\mathrm{leaf}(v', s'))$ for any $v', s'$, the result is $\mathrm{none}$ (the leaf's own $v', s'$ are discarded and not compared with $v, s$);
- if $W = \mathrm{inl}(\mathrm{branch}(l, r))$, the result is
  $$\mathrm{some}\big(\mathrm{taggedPre}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s)),\; \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(\mathrm{hash}(l), \mathrm{hash}(r)))\big).$$

Here $\mathrm{controlNodes}(\mathit{control})$ is the preamble's function: let $m = \lfloor (|\mathit{control}| \dot{-} 33) / 32 \rfloor$, where $\dot{-}$ is truncated natural-number subtraction (so $m = 0$ whenever $|\mathit{control}| < 33 + 32$); the result is the list of $m$ byte strings obtained from $\mathit{control}$ with its first 33 bytes dropped by repeatedly taking the first 32 bytes and dropping them (each of the $m$ chunks is a full 32 bytes, since the dropped string has at least $32m$ bytes); any trailing bytes beyond the $m$ chunks are ignored. In particular, if $|\mathit{control}| < 65$ the path is empty, the walk returns $\mathrm{inl}(T)$, and the witness is $\mathrm{none}$ if $T$ is a leaf and the pair above (with $l, r$ the root's children) if $T$ is a branch. The function performs no check that the folded root equals $\mathrm{hash}(T)$ and no check that a returned pair collides.

## 11. `TweakCollision`

For byte strings $q, t_1, t_2$, a Boolean $\mathit{parity}$, and a pair of natural numbers $P = (P_x, P_y)$, $\mathrm{TweakCollision}(q, \mathit{parity}, P, t_1, t_2)$ is the proposition

$$t_1 \neq t_2 \;\wedge\; |t_1| = 32 \;\wedge\; |t_2| = 32 \;\wedge\; \mathrm{xonlyTweakAddCheck}(q, \mathit{parity}, P, t_1) = \mathrm{true} \;\wedge\; \mathrm{xonlyTweakAddCheck}(q, \mathit{parity}, P, t_2) = \mathrm{true}.$$

Here $\mathrm{xonlyTweakAddCheck}(\mathit{out}, \mathit{parity}, P, \mathit{tw})$ is the preamble's Boolean function: let $t = \mathrm{beVal}(\mathit{tw})$ be the big-endian natural-number value of the byte string $\mathit{tw}$ (fold $\mathit{acc} \mapsto 256\,\mathit{acc} + \text{byte}$ from $0$); if $t \ge n$ (the secp256k1 group order constant $n = \mathtt{0xFFFFFFFF\ldots BFD25E8CD0364141}$) the result is false; otherwise compute $Q = \mathrm{padd}(\mathrm{some}(P), \mathrm{pmul}(t, G))$, where $G = (G_x, G_y)$ is the secp256k1 base-point constant, $\mathrm{pmul}$ is double-and-add scalar multiplication with 257 steps of fuel starting from the point at infinity (so $\mathrm{pmul}(0, G)$ is the point at infinity), and $\mathrm{padd}$ is affine addition on points-or-infinity modulo the field prime $p = 2^{256} - 2^{32} - 977$ (infinity is the identity; two points with $x_1 \equiv x_2 \pmod p$ give infinity when $y_1 + y_2 \equiv 0 \pmod p$ and otherwise the doubling formula with the field inverse computed by Fermat exponentiation, where $0$ inverts to $0$; otherwise the chord formula); if $Q$ is infinity the result is false; otherwise, with $Q = (q_x, q_y)$, the result is $\big[\mathrm{be32}(q_x) = \mathit{out}\big] \wedge \big[(q_y \bmod 2 = 1) = \mathit{parity}\big]$, where $\mathrm{be32}(x)$ is the 32-byte big-endian encoding of $x$ (reduced modulo $2^{256}$). Nothing in $\mathrm{TweakCollision}$ requires $P$ to lie on the curve, $q$ to have length 32, or $t_1, t_2$ to be related to any hash.

## 12. `HonestOutput`

For byte strings $q$ and $\mathit{internal32}$, a Boolean $\mathit{parity}$, and a tree $T$, $\mathrm{HonestOutput}(q, \mathit{internal32}, \mathit{parity}, T)$ is the proposition

$$\mathrm{checkTapTweak}(q, \mathit{internal32}, \mathrm{hash}(T), \mathit{parity}) = \mathrm{true},$$

where the preamble's $\mathrm{checkTapTweak}(q, i, \mathit{root}, \mathit{parity})$ is: if $\mathrm{liftX}(\mathrm{beVal}(i))$ is $\mathrm{none}$ the value is false; otherwise, with $\mathrm{liftX}(\mathrm{beVal}(i)) = \mathrm{some}(P)$, the value is $\mathrm{xonlyTweakAddCheck}(q, \mathit{parity}, P, \mathrm{tapTweakHash}(i, \mathit{root}))$. Here $\mathrm{tapTweakHash}(i, \mathit{root}) = \mathrm{tagged}(\text{"TapTweak"}, i \,\|\, \mathit{root})$, and $\mathrm{liftX}(x)$ is: $\mathrm{none}$ if $x \ge p$; otherwise let $y = (x^3 + 7)^{(p+1)/4} \bmod p$; if $y^2 \equiv x^3 + 7 \pmod p$ then $\mathrm{some}(x, y')$ with $y'$ the one of $y$ and $(p - y) \bmod p$ that is even, else $\mathrm{none}$. No length constraint is placed on $q$ or $\mathit{internal32}$ by this definition itself; $\mathrm{beVal}$ of a string of any length is a natural number.

## 13. `controlInternalKey`

For a byte string $\mathit{control}$,

$$\mathrm{controlInternalKey}(\mathit{control}) = \mathrm{take}_{32}(\mathrm{drop}_1(\mathit{control})),$$

the bytes at positions $1$ through $32$ (0-based). If $\mathit{control}$ has fewer than 33 bytes the result is correspondingly shorter (empty when $|\mathit{control}| \le 1$).

## 14. `controlParity`

For a byte string $\mathit{control}$,

$$\mathrm{controlParity}(\mathit{control}) = \big[\, (\mathit{control}[0] \text{ with default } 0)\bmod 2 = 1 \,\big],$$

a Boolean: true exactly when the first byte of $\mathit{control}$ is odd, where a missing first byte (empty $\mathit{control}$) is read as the byte $0$, giving false.
