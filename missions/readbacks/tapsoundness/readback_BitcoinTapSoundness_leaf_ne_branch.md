# Read-back: `BitcoinTapSoundness.leaf_ne_branch`

**Statement.** For every byte $v$ (an 8-bit value) and all byte strings $s, a, b$ (finite sequences of 8-bit values, of **any** lengths, including empty — there are no length hypotheses at all in this theorem), if

$$
\mathrm{LeafHash}(v, s) \;=\; \mathrm{BranchHash}(a, b),
$$

then $\mathsf{Sha256Collision}$ holds, i.e. there exist two byte strings $x \neq y$ (of any lengths, unrelated to $v, s, a, b$) with $\mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

**Unfolded notions.**

- $\mathrm{SHA256}$ is the bundle's own executable implementation of SHA-256, a total function from all finite byte strings to 32-byte strings.
- $\mathrm{utf8}(\cdot)$ is UTF-8 encoding; for a tag string $\tau$,
$$
\mathrm{Tagged}_{\tau}(m) := \mathrm{SHA256}\bigl(\mathrm{SHA256}(\mathrm{utf8}(\tau)) \| \mathrm{SHA256}(\mathrm{utf8}(\tau)) \| m\bigr).
$$
- $\mathrm{CS}(\ell)$ is Bitcoin's "compact size" encoding of the natural number $\ell$: the single byte $\ell$ if $\ell < 253$; the byte $0xfd$ followed by $\ell$ as 2 little-endian bytes if $253 \le \ell \le 65535$; the byte $0xfe$ followed by 4 little-endian bytes if $\ell \le 2^{32}-1$; otherwise the byte $0xff$ followed by 8 little-endian bytes of $\ell \bmod 2^{64}$.
- The leaf hash is
$$
\mathrm{LeafHash}(v, s) := \mathrm{Tagged}_{\text{``TapLeaf''}}\bigl([v] \,\|\, \mathrm{CS}(|s|) \,\|\, s\bigr),
$$
  where $[v]$ is the one-byte string containing $v$ (used as given, with no masking of its low bit).
- $\prec$ is lexicographic order on byte strings (first differing byte decides; a proper prefix is smaller; no string is $\prec$ itself), and
$$
\mathrm{BranchHash}(a, b) := \mathrm{Tagged}_{\text{``TapBranch''}}\bigl(\text{if } a \prec b \text{ then } a\|b \text{ else } b\|a\bigr).
$$
- $\mathsf{Sha256Collision}$ is the closed proposition $\exists\, x, y \in \mathsf{Bytes}.\; x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$; it does not depend on $v, s, a, b$. Since it concerns a fixed total function from infinitely many inputs to finitely many 32-byte outputs, its truth value is a fixed mathematical fact (such a pair exists by counting), not an assumption.

**Edge cases made explicit.** $s$, $a$, $b$ may be empty or of arbitrary and unequal lengths; $a$ may equal $b$. Both sides of the hypothesis are 32-byte digests, so the hypothesis is an equality of 32-byte strings. The conclusion mentions none of $v, s, a, b$.
