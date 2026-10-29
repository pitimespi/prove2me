# Read-back: `BitcoinTapSoundnessV2.tapleaf_ne_tapbranch`

**Statement.** A closed proposition with no binders and no hypotheses:

$$\mathrm{SHA256}\big(\mathrm{ascii}(\text{"TapLeaf"})\big) \;\neq\; \mathrm{SHA256}\big(\mathrm{ascii}(\text{"TapBranch"})\big).$$

**Unfoldings.** $\mathrm{ascii}(t)$ is the list of UTF-8 code units of the string $t$, each taken as one 8-bit byte; so $\mathrm{ascii}(\text{"TapLeaf"})$ is the 7-byte string $[\mathtt{0x54}, \mathtt{0x61}, \mathtt{0x70}, \mathtt{0x4c}, \mathtt{0x65}, \mathtt{0x61}, \mathtt{0x66}]$ and $\mathrm{ascii}(\text{"TapBranch"})$ is the 9-byte string $[\mathtt{0x54}, \mathtt{0x61}, \mathtt{0x70}, \mathtt{0x42}, \mathtt{0x72}, \mathtt{0x61}, \mathtt{0x6e}, \mathtt{0x63}, \mathtt{0x68}]$. $\mathrm{SHA256}$ is the bundle's executable SHA-256: a total function on byte strings that appends the byte $\mathtt{0x80}$, zero bytes until the length is $\equiv 56 \pmod{64}$, and the original bit-length as 8 big-endian bytes; splits the padded string into 64-byte chunks; folds the SHA-256 compression function (message schedule, 64 rounds with the standard round constants) over the chunks from the standard initial state; and emits the eight 32-bit state words as big-endian 4-byte groups, a 32-byte string.

**What is asserted.** The two 32-byte strings obtained by applying this concrete function to these two concrete byte strings are different byte strings (they differ in at least one of their 32 positions). Nothing is asserted about any other tag, about the tagged-hash construction, or about collision resistance in general; the statement concerns exactly these two fixed inputs.
