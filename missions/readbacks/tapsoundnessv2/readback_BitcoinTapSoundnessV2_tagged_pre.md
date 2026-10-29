# Read-back: `BitcoinTapSoundnessV2.tagged_pre`

**Statement.** For every string $t$ and every byte string $m$ (a finite list of 8-bit bytes, of any length including empty),

$$\mathrm{tagged}(t, m) \;=\; \mathrm{SHA256}\big(\mathrm{taggedPre}(t, m)\big).$$

**Unfoldings.** $\mathrm{SHA256}$ is the bundle's executable SHA-256: a total function on byte strings that appends the byte $\mathtt{0x80}$, zero bytes until the length is $\equiv 56 \pmod{64}$, and the original bit-length as 8 big-endian bytes; splits into 64-byte chunks; folds the SHA-256 compression function over them from the standard initial state; and emits the eight 32-bit state words as big-endian 4-byte groups. $\mathrm{ascii}(t)$ is the list of UTF-8 code units of $t$, each as a byte.

The left-hand side, $\mathrm{tagged}(t, m)$, is defined in the preamble as $\mathrm{taggedHash}(\mathrm{ascii}(t), m)$, where $\mathrm{taggedHash}(\mathit{tag}, m)$ lets $\theta = \mathrm{SHA256}(\mathit{tag})$ and returns $\mathrm{SHA256}(\theta \| \theta \| m)$; so

$$\mathrm{tagged}(t, m) = \mathrm{SHA256}\big(\mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, m\big).$$

The right-hand side uses $\mathrm{taggedPre}(t, m) = \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, m$, so the right-hand side is

$$\mathrm{SHA256}\big(\mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, \mathrm{SHA256}(\mathrm{ascii}(t)) \,\|\, m\big).$$

**Edge cases and what is silently included.** The statement is an equality of byte strings (32-byte outputs of $\mathrm{SHA256}$) with no hypotheses; it holds for the empty string $t$ and the empty byte string $m$ as well. Both sides unfold to the same expression; the theorem asserts nothing about collisions, distinctness, or any property of $\mathrm{SHA256}$ beyond its being a function.
