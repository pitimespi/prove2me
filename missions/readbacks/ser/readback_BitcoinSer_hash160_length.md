# Read-back: `BitcoinSer.hash160_length`

**Binders and hypothesis.** A single byte string $m$, universally quantified, with no restriction (empty or of any length). No hypotheses.

**Conclusion.** The composite hash $\texttt{hash160}$ applied to $m$ is a byte string of length exactly 20:
$$|\texttt{hash160}(m)| = 20 .$$

**Unfolding.** By definition $\texttt{hash160}(m) = \texttt{ripemd160}(\texttt{sha256}(m))$: the file's SHA-256 is applied first, producing (by its definition) a 32-byte string, and the file's RIPEMD-160 is applied to that. The statement, however, only requires the outer function's output length. $\texttt{ripemd160}(x)$ is defined as: pad $x$ with $\texttt{mdPad}\;\mathrm{false}$ (append $\mathrm{0x80}$, then zeros to reach 56 mod 64, then the 8 **little-endian** bytes of the bit length $8|x|$); cut into 64-byte chunks; fold $\texttt{ripemdCompress}$ over the chunks starting from the 5-word initial state $(\mathrm{0x67452301}, \mathrm{0xEFCDAB89}, \mathrm{0x98BADCFE}, \mathrm{0x10325476}, \mathrm{0xC3D2E1F0})$, where each compression runs two independent 80-step lines (left and right) over the chunk's 16 little-endian words, using the 80-entry index tables and 80-entry rotation tables, and recombines the two results with the input state by the five cross-sums $(b + L_c + R_d,\; c + L_d + R_e,\; d + L_e + R_a,\; e + L_a + R_b,\; a + L_b + R_c)$; finally the five 32-bit state words are each emitted as 4 **little-endian** bytes.

The length claim thus reduces to: five concatenated outputs of $\texttt{le32Bytes}$, each $\texttt{leBytes}\;4$ of a word value and hence of length 4, total $5 \times 4 = 20$. Neither the number of chunks nor the inner SHA-256 value affects this. Since the inner input to RIPEMD-160 is always the 32-byte SHA-256 output, the RIPEMD-160 stage always processes exactly one 64-byte padded chunk (32 + 1 + 23 + 8 = 64), but the theorem does not depend on or state this.

**What is not said.** Nothing about the byte values, agreement with any standard Hash160/RIPEMD-160, or any test vector. Nothing about the length of $\texttt{ripemd160}$ on its own (only the composite is named), nor of $\texttt{sha256}$ (that is `sha256_length`), nor $\texttt{sha1}$. No injectivity or collision statement. No statement that the padded input has a multiple-of-64 length. The theorem fixes only the output length, 20, for every input $m$.
