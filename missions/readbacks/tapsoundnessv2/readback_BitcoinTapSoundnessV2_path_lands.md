# Read-back: `BitcoinTapSoundnessV2.path_lands`

**Binders and hypotheses.** For every tree $T$ of type $\mathrm{TapTree}$ (built from $\mathrm{leaf}(v, s)$, $v$ a byte and $s$ a byte string, and $\mathrm{branch}(l, r)$), every list of byte strings $\mathit{nodes} = [n_1, \dots, n_k]$ (with $k \ge 0$), and every byte string $h$, such that

- $\mathit{hn}$: every element $n$ of $\mathit{nodes}$ has $|n| = 32$;
- $\mathit{hh}$: $|h| = 32$;
- $\mathit{heq}$: the left fold of $\mathrm{tapbranchHash}$ over $\mathit{nodes}$ starting from $h$ equals $\mathrm{hash}(T)$, i.e. with $h_0 = h$ and $h_i = \mathrm{tapbranchHash}(h_{i-1}, n_i)$, $h_k = \mathrm{hash}(T)$;

**Conclusion.** at least one of the following holds (inclusive disjunction):

1. there exists a tree $U$ such that
   $$\mathrm{walk}(T, \mathit{nodes}, h) = \mathrm{inl}(U), \qquad U \in \mathrm{subtreesAt}(T, k), \qquad \mathrm{hash}(U) = h;$$
   or
2. there exist byte strings $x, y$ such that
   $$\mathrm{walk}(T, \mathit{nodes}, h) = \mathrm{inr}(x, y) \quad\text{and}\quad \mathrm{Collides}(x, y).$$

**Unfoldings.** $\mathrm{SHA256}$ is the bundle's executable SHA-256 (MD padding, 64-byte-chunk compression from the standard IV, eight big-endian words out), total on byte strings. $\mathrm{ascii}(t)$ is the UTF-8 byte list of $t$; $\mathrm{tagged}(t, m) = \mathrm{SHA256}(\mathrm{SHA256}(\mathrm{ascii}(t)) \| \mathrm{SHA256}(\mathrm{ascii}(t)) \| m)$; $\mathrm{taggedPre}(t, m) = \mathrm{SHA256}(\mathrm{ascii}(t)) \| \mathrm{SHA256}(\mathrm{ascii}(t)) \| m$. $\mathrm{Collides}(x, y)$ is $x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

$\mathrm{writeCompactSize}(n)$: one byte $n$ if $n < 253$, else a marker byte ($253$/$254$/$255$) followed by 2/4/8 little-endian bytes according to $n \le \mathtt{0xffff}$ / $\le \mathtt{0xffffffff}$ / larger. $\mathrm{leafMsg}(v, s) = [v] \| \mathrm{writeCompactSize}(|s|) \| s$; $\mathrm{tapleafHash}(v, s) = \mathrm{tagged}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s))$. $\mathrm{lexLt}$ is Boolean strict lexicographic order on byte strings; $\mathrm{branchMsg}(a, b) = a \| b$ if $\mathrm{lexLt}(a, b)$ else $b \| a$; $\mathrm{tapbranchHash}(a, b) = \mathrm{tagged}(\text{"TapBranch"}, \mathrm{branchMsg}(a, b))$.

$\mathrm{hash}(\mathrm{leaf}(v, s)) = \mathrm{tapleafHash}(v, s)$; $\mathrm{hash}(\mathrm{branch}(l, r)) = \mathrm{tapbranchHash}(\mathrm{hash}(l), \mathrm{hash}(r))$.

$\mathrm{subtreesAt}(T, 0) = [T]$; $\mathrm{subtreesAt}(\mathrm{leaf}(v, s), d+1) = []$; $\mathrm{subtreesAt}(\mathrm{branch}(l, r), d+1) = \mathrm{subtreesAt}(l, d) \| \mathrm{subtreesAt}(r, d)$. $U \in \mathrm{subtreesAt}(T, k)$ is list membership (equality of trees, which is decidable).

$\mathrm{walk}(T, \mathit{path}, h)$ returns either a tree ($\mathrm{inl}$) or a pair of byte strings ($\mathrm{inr}$), case by case: $\mathrm{walk}(T, [], h) = \mathrm{inl}(T)$ for every $h$. For a path $n :: \mathit{rest}$, let $W = \mathrm{walk}(T, \mathit{rest}, \mathrm{tapbranchHash}(h, n))$; if $W = \mathrm{inr}(c)$ the result is $\mathrm{inr}(c)$; if $W = \mathrm{inl}(\mathrm{leaf}(v, s))$ the result is $\mathrm{inr}\big(\mathrm{taggedPre}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s)), \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(h, n))\big)$; if $W = \mathrm{inl}(\mathrm{branch}(l, r))$ the result is $\mathrm{inl}(l)$ when $h = \mathrm{hash}(l)$, otherwise $\mathrm{inl}(r)$ when $h = \mathrm{hash}(r)$, otherwise $\mathrm{inr}\big(\mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(\mathrm{hash}(l), \mathrm{hash}(r))), \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(h, n))\big)$. Unwound on $[n_1, \dots, n_k]$: the innermost call is on $h_k$ and the empty path and returns $\mathrm{inl}(T)$; the step for $n_k$ compares $h_{k-1}$ with the children of $T$; the step for $n_{k-1}$ compares $h_{k-2}$ with the children of the chosen child; and so on, so the tree is descended from the root while the list is read from its end, and the final comparison (for $n_1$) is of $h_0 = h$. The function performs no length or root check of its own.

**Edge cases and what is silently included.** When $k = 0$ ($\mathit{nodes}$ empty): $\mathit{hn}$ is vacuous, $\mathit{heq}$ reads $h = \mathrm{hash}(T)$, $\mathrm{walk}$ returns $\mathrm{inl}(T)$, and $\mathrm{subtreesAt}(T, 0) = [T]$, so alternative 1 is $U = T$. When $k$ exceeds the depth of every node reached, $\mathrm{subtreesAt}(T, k)$ is empty, so alternative 1 cannot hold and the statement reduces to alternative 2. Alternative 2 asserts that the specific pair $(x, y)$ returned by $\mathrm{walk}$ — an explicit expression in $T$, the $n_i$ and $h$ — consists of two different byte strings with equal SHA-256; alternative 1 asserts no collision. The disjunction is inclusive. The trees' leaves are unconstrained (any byte $v$, any script length), and $\mathrm{hash}(T)$ is always a 32-byte string by construction, so $\mathit{heq}$ compares 32-byte strings.
