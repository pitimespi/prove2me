# Read-back: `BitcoinTapSoundnessV2.tagged_collision`

**Statement.** For all strings $t, t'$ and all byte strings $m, m'$ (finite lists of 8-bit bytes, any length), if

$$\mathrm{tagged}(t, m) = \mathrm{tagged}(t', m'),$$

then at least one of the following holds (inclusive disjunction):

1. $\mathrm{SHA256}(\mathrm{ascii}(t)) = \mathrm{SHA256}(\mathrm{ascii}(t'))$ and $m = m'$; or
2. $\mathrm{Collides}\big(\mathrm{taggedPre}(t, m),\; \mathrm{taggedPre}(t', m')\big)$.

**Unfoldings.** $\mathrm{SHA256}$ is the bundle's executable SHA-256: a total function on byte strings that appends $\mathtt{0x80}$, zero bytes until the length is $\equiv 56 \pmod{64}$, and the original bit-length as 8 big-endian bytes, then folds the SHA-256 compression function over the 64-byte chunks from the standard initial state and outputs the eight 32-bit state words big-endian (32 bytes). $\mathrm{ascii}(t)$ is the list of UTF-8 code units of the string $t$, each as a byte. $\mathrm{tagged}(t, m)$ is the preamble's $\mathrm{taggedHash}(\mathrm{ascii}(t), m)$, i.e.

$$\mathrm{tagged}(t, m) = \mathrm{SHA256}\big(\mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, m\big),$$

and $\mathrm{taggedPre}(t, m) = \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, m$, a string of length $64 + |m|$. $\mathrm{Collides}(x, y)$ is $x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

**Edge cases and what is silently included.** Alternative 1 does *not* assert $t = t'$: it asserts only that the two tag strings have the same SHA-256 (which holds in particular when $t = t'$, and would also hold for two different strings with colliding hashes) together with $m = m'$. Alternative 2 names the two explicit $(64 + |m|)$- and $(64 + |m'|)$-byte preimages and asserts that they are different byte strings and have equal SHA-256; the equal-SHA-256 part is, by unfolding, the hypothesis itself, so the additional content of alternative 2 is $\mathrm{taggedPre}(t, m) \neq \mathrm{taggedPre}(t', m')$. Either or both alternatives may hold. The strings $t, t'$ may be empty, and $m, m'$ may be empty or of different lengths.
