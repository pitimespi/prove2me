# Read-back: `BitcoinTapSoundness.tapleaf_ne_tapbranch`

**Statement.** This is a closed statement with no variables and no hypotheses:

$$
\mathrm{SHA256}\bigl(\mathrm{utf8}(\text{``TapLeaf''})\bigr) \;\neq\; \mathrm{SHA256}\bigl(\mathrm{utf8}(\text{``TapBranch''})\bigr).
$$

That is, the 32-byte SHA-256 digest of the 7-byte ASCII/UTF-8 encoding of the string `TapLeaf` (bytes $0x54\,0x61\,0x70\,0x4c\,0x65\,0x61\,0x66$) is not equal, as a byte string, to the 32-byte SHA-256 digest of the 9-byte encoding of the string `TapBranch` (bytes $0x54\,0x61\,0x70\,0x42\,0x72\,0x61\,0x6e\,0x63\,0x68$).

**Unfolded notions.**

- $\mathrm{utf8}(t)$ is the list of bytes of the UTF-8 encoding of the string $t$; for these two ASCII strings it is their ASCII bytes.
- $\mathrm{SHA256}$ is the bundle's own executable implementation of SHA-256: Merkle–Damgård padding (append $0x80$, then zero bytes until the length is $56 \bmod 64$, then the message bit length as 8 big-endian bytes), the standard 64-round compression function with the standard round constants and initial state, and a 32-byte big-endian digest. It is a concrete total function, so both sides of the inequality are specific, computable 32-byte strings.

**Edge cases made explicit.** Nothing is quantified; the statement is simply the inequality of two particular 32-byte values determined by the implementation. It does not mention tagged hashes, leaves, branches, or the tapleaf/tapbranch hash functions themselves; it compares only the plain SHA-256 digests of the two tag strings.
