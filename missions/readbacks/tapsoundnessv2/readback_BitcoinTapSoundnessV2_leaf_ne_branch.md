# Read-back: `BitcoinTapSoundnessV2.leaf_ne_branch`

**Statement.** For every byte $v$ (an 8-bit vector) and all byte strings $s, a, b$ (finite lists of bytes, of any length including empty), if

$$\mathrm{tapleafHash}(v, s) = \mathrm{tapbranchHash}(a, b),$$

then

$$\mathrm{Collides}\big(\mathrm{taggedPre}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s)),\; \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(a, b))\big).$$

**Unfoldings.** $\mathrm{SHA256}$ is the bundle's executable SHA-256 (MD padding with $\mathtt{0x80}$, zeros to $56 \bmod 64$, 8-byte big-endian bit length; compression of each 64-byte chunk from the standard initial state; eight big-endian 32-bit words out), a total function on byte strings. $\mathrm{ascii}(t)$ is the UTF-8 byte list of the string $t$. $\mathrm{tagged}(t, m) = \mathrm{SHA256}\big(\mathrm{SHA256}(\mathrm{ascii}(t)) \| \mathrm{SHA256}(\mathrm{ascii}(t)) \| m\big)$ and $\mathrm{taggedPre}(t, m) = \mathrm{SHA256}(\mathrm{ascii}(t)) \| \mathrm{SHA256}(\mathrm{ascii}(t)) \| m$.

$\mathrm{writeCompactSize}(n)$ is one byte $n$ if $n < 253$; byte $253$ then 2 little-endian bytes of $n$ if $n \le \mathtt{0xffff}$; byte $254$ then 4 LE bytes if $n \le \mathtt{0xffffffff}$; else byte $255$ then 8 LE bytes. $\mathrm{leafMsg}(v, s) = [v] \| \mathrm{writeCompactSize}(|s|) \| s$, and $\mathrm{tapleafHash}(v, s) = \mathrm{tagged}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s))$.

$\mathrm{lexLt}$ is the Boolean strict lexicographic order on byte strings ($[]$ is below any non-empty string; otherwise compare leading bytes and recurse on ties; $\mathrm{lexLt}(x, x)$ is false). $\mathrm{branchMsg}(a, b) = a \| b$ if $\mathrm{lexLt}(a, b)$, else $b \| a$. $\mathrm{tapbranchHash}(a, b) = \mathrm{tagged}(\text{"TapBranch"}, \mathrm{branchMsg}(a, b))$.

$\mathrm{Collides}(x, y)$ is $x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

**Edge cases and what is silently included.** There are no length hypotheses: $s$, $a$ and $b$ may have any length (including $0$), and $a, b$ need not be 32 bytes or hashes of anything; $v$ may be any byte. The conclusion names two explicit strings — the "TapLeaf"-prefixed preimage of the leaf hash, $\mathrm{SHA256}(\mathrm{ascii}(\text{"TapLeaf"}))^{2} \| [v] \| \mathrm{writeCompactSize}(|s|) \| s$, and the "TapBranch"-prefixed preimage of the branch hash, $\mathrm{SHA256}(\mathrm{ascii}(\text{"TapBranch"}))^{2} \| \mathrm{branchMsg}(a, b)$ (where $X^2$ abbreviates $X \| X$) — and asserts (i) they are different byte strings and (ii) their SHA-256 outputs coincide. Part (ii) is, by unfolding, the hypothesis itself; part (i) is the additional content. The two strings differ in their first 64 bytes exactly when $\mathrm{SHA256}(\mathrm{ascii}(\text{"TapLeaf"})) \neq \mathrm{SHA256}(\mathrm{ascii}(\text{"TapBranch"}))$, which this theorem does not itself assert.
