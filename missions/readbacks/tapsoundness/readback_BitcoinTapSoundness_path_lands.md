# Read-back: `BitcoinTapSoundness.path_lands`

**Statement.** Let $T$ be a tap tree (a finite binary tree in which every internal node has exactly two ordered children and every leaf carries a byte $v$ and a byte string $s$). Let $\mathit{nodes} = [n_1, n_2, \dots, n_\ell]$ be a finite list of byte strings (possibly empty, $\ell = 0$), and let $h$ be a byte string. Assume

- every element $n_i$ of $\mathit{nodes}$ has length exactly $32$;
- $|h| = 32$;
- the left fold of the branch hash over the list starting from $h$ equals the hash of $T$:
$$
\mathrm{BranchHash}\bigl(\cdots \mathrm{BranchHash}(\mathrm{BranchHash}(h, n_1), n_2) \cdots, n_\ell\bigr) \;=\; \mathrm{hash}(T),
$$
  (for $\ell = 0$ the left-hand side is just $h$).

Then at least one of the following holds:

1. there exists a subtree $U$ occurring in the list $\mathrm{subtreesAt}(T, \ell)$ of subtrees of $T$ at depth exactly $\ell$ (where $\ell = |\mathit{nodes}|$) such that $\mathrm{hash}(U) = h$; or
2. $\mathsf{Sha256Collision}$: there exist two byte strings $x \neq y$ (of any lengths, unrelated to $T, \mathit{nodes}, h$) with $\mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

**Unfolded notions.**

- $\mathrm{SHA256}$ is the bundle's own executable implementation of SHA-256 (a total function from all finite byte strings to 32-byte strings). $\mathrm{utf8}(\cdot)$ is UTF-8 encoding, and for a tag string $\tau$,
$$
\mathrm{Tagged}_{\tau}(m) := \mathrm{SHA256}\bigl(\mathrm{SHA256}(\mathrm{utf8}(\tau)) \| \mathrm{SHA256}(\mathrm{utf8}(\tau)) \| m\bigr).
$$
- $\mathrm{CS}(\cdot)$ is the compact-size encoding of a natural number (one byte below 253; $0xfd$ + 2 little-endian bytes up to $65535$; $0xfe$ + 4 bytes up to $2^{32}-1$; $0xff$ + 8 bytes of the value mod $2^{64}$ otherwise).
- $\mathrm{LeafHash}(v, s) := \mathrm{Tagged}_{\text{``TapLeaf''}}([v] \| \mathrm{CS}(|s|) \| s)$.
- $\prec$ is lexicographic order on byte strings (first differing byte decides by numeric value; a proper prefix is smaller; no string is $\prec$ itself) and
$$
\mathrm{BranchHash}(a, b) := \mathrm{Tagged}_{\text{``TapBranch''}}\bigl(\text{if } a \prec b \text{ then } a\|b \text{ else } b\|a\bigr),
$$
  which is symmetric in $a, b$.
- The hash of a tap tree is defined recursively: $\mathrm{hash}(\mathrm{leaf}(v, s)) := \mathrm{LeafHash}(v, s)$ and $\mathrm{hash}(\mathrm{branch}(L, R)) := \mathrm{BranchHash}(\mathrm{hash}(L), \mathrm{hash}(R))$.
- The list of subtrees at depth $d$ is defined recursively: $\mathrm{subtreesAt}(T, 0) := [T]$ for any $T$; $\mathrm{subtreesAt}(\mathrm{leaf}(v,s), d+1) := []$ (the empty list); $\mathrm{subtreesAt}(\mathrm{branch}(L,R), d+1) := \mathrm{subtreesAt}(L, d) \,\|\, \mathrm{subtreesAt}(R, d)$ (list concatenation). So it lists, left to right, exactly the subtrees rooted at depth $d$; it is empty when $d$ exceeds the depth of every leaf along the way.
- $\mathsf{Sha256Collision}$ is the closed proposition $\exists\, x, y \in \mathsf{Bytes}.\; x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$, independent of all the theorem's variables; since it concerns a fixed total function from infinitely many inputs to finitely many 32-byte outputs, its truth value is a fixed mathematical fact (such a pair exists by counting), not an assumption.

**Edge cases made explicit.** When $\mathit{nodes}$ is empty, the hypothesis reads $h = \mathrm{hash}(T)$ and $\mathrm{subtreesAt}(T, 0) = [T]$, so disjunct (1) is exactly that hypothesis. When $\ell$ is larger than the depth of $T$ (e.g. $T$ is a single leaf and $\ell \ge 1$), $\mathrm{subtreesAt}(T, \ell)$ is empty, so disjunct (1) is false and the theorem then asserts $\mathsf{Sha256Collision}$ outright under the hypotheses. The fold passes the accumulator as the *first* argument of $\mathrm{BranchHash}$ and the node as the second, but the result does not depend on this because $\mathrm{BranchHash}$ is symmetric. The leaf-version bytes and scripts inside $T$ are unconstrained.
