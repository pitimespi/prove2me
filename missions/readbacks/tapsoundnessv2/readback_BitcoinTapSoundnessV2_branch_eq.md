# Read-back: `BitcoinTapSoundnessV2.branch_eq`

**Statement.** For all byte strings $a, b, c, d$ (finite lists of 8-bit bytes) such that

$$|a| = 32, \quad |b| = 32, \quad |c| = 32, \quad |d| = 32,$$

and such that

$$\mathrm{tapbranchHash}(a, b) = \mathrm{tapbranchHash}(c, d),$$

at least one of the following holds (inclusive disjunction):

1. $(a = c \wedge b = d)$ or $(a = d \wedge b = c)$ — the two unordered pairs $\{a, b\}$ and $\{c, d\}$ coincide as ordered pairs up to swapping; or

2. $\mathrm{Collides}\big(\mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(a, b)),\; \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(c, d))\big)$.

**Unfoldings.** $\mathrm{SHA256}$ is the bundle's executable SHA-256 (MD padding with $\mathtt{0x80}$, zeros to $56 \bmod 64$, 8-byte big-endian bit length; compression over 64-byte chunks from the standard initial state; eight big-endian 32-bit words out), a total function on byte strings. $\mathrm{ascii}(t)$ is the UTF-8 byte list of the string $t$. $\mathrm{tagged}(t, m) = \mathrm{SHA256}\big(\mathrm{SHA256}(\mathrm{ascii}(t)) \| \mathrm{SHA256}(\mathrm{ascii}(t)) \| m\big)$, and $\mathrm{taggedPre}(t, m) = \mathrm{SHA256}(\mathrm{ascii}(t)) \| \mathrm{SHA256}(\mathrm{ascii}(t)) \| m$ (a string of length $64 + |m|$).

$\mathrm{lexLt}(x, y)$ is the Boolean strict lexicographic order on byte strings: $\mathrm{lexLt}([],[]) = \mathrm{false}$, $\mathrm{lexLt}([], y{::}ys) = \mathrm{true}$, $\mathrm{lexLt}(x{::}xs, []) = \mathrm{false}$, and $\mathrm{lexLt}(x{::}xs, y{::}ys)$ is true if byte $x <$ byte $y$, false if $y < x$, else $\mathrm{lexLt}(xs, ys)$. $\mathrm{branchMsg}(x, y) = x \| y$ if $\mathrm{lexLt}(x, y)$ and $y \| x$ otherwise (so $\mathrm{branchMsg}(x, x) = x \| x$). $\mathrm{tapbranchHash}(x, y) = \mathrm{tagged}(\text{"TapBranch"}, \mathrm{branchMsg}(x, y))$; in particular $\mathrm{tapbranchHash}(x, y) = \mathrm{tapbranchHash}(y, x)$ by unfolding.

$\mathrm{Collides}(x, y)$ means $x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$: the two 128-byte strings in disjunct 2 must be *distinct* as byte strings and have the same SHA-256 output.

**Edge cases and what is silently included.** All four inputs are required to have length exactly 32; no other constraint (e.g. being a hash of anything) is imposed. When $a = b$, $\mathrm{branchMsg}(a, b) = a \| a$. Disjunct 1 is an equality of byte strings, so it is satisfied e.g. whenever $(a,b) = (c,d)$. Disjunct 2 is a stronger claim than the mere existence of a collision: it names the two specific preimages $\mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(a,b))$ and $\mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(c,d))$ and asserts they differ and hash equal. Since $\mathrm{tapbranchHash}(a,b)$ is by unfolding $\mathrm{SHA256}$ of the first of these strings and $\mathrm{tapbranchHash}(c,d)$ is $\mathrm{SHA256}$ of the second, the hypothesis already gives equal SHA-256 outputs; the content of disjunct 2 beyond the hypothesis is $\mathrm{branchMsg}(a,b) \neq \mathrm{branchMsg}(c,d)$ (the shared 64-byte prefix being identical).
