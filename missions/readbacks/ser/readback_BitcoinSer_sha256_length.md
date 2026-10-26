# Read-back: `BitcoinSer.sha256_length`

**Binders and hypothesis.** A single byte string $m$ (a finite list of 8-bit values), universally quantified with no restriction: $m$ may be empty, may have any length including lengths that are not multiples of 64, and may be arbitrarily long. There are no hypotheses.

**Conclusion.** The output of the file's own SHA-256 function on $m$ has exactly 32 bytes:
$$|\texttt{sha256}(m)| = 32 .$$

**Unfolding.** $\texttt{sha256}(m)$ is defined as follows. First the message is padded by $\texttt{mdPad}\;\mathrm{true}$: append the byte $\mathrm{0x80}$, then $(119 - (|m| \bmod 64)) \bmod 64$ zero bytes, then the 8 big-endian bytes of $8|m|$ (mod $2^{64}$). The padded string is cut into 64-byte chunks by $\texttt{chunks64}$ (any trailing partial chunk would be discarded, though the padding always produces a multiple of 64). Starting from the 8-word initial state $(\mathrm{0x6a09e667}, \dots, \mathrm{0x5be0cd19})$, each chunk is processed by $\texttt{sha256Compress}$: the chunk's 16 big-endian 32-bit words are expanded to 64 by the schedule $\sigma_1(w_{t-2}) + w_{t-7} + \sigma_0(w_{t-15}) + w_{t-16}$, each schedule word is added to the matching entry of the 64-entry constant table, 64 rounds are folded over the state, and the result is added word-wise to the chunk's input state. Finally the eight 32-bit state words $a, b, \dots, h$ are each written as 4 big-endian bytes and concatenated.

The theorem is therefore equivalent to: eight applications of $\texttt{be32Bytes}$ (each of which is $\texttt{beBytes}\;4$, the reversal of $\texttt{leBytes}\;4$, hence of length 4) concatenated give $8 \times 4 = 32$ bytes. The number of chunks, the content of the state, and the message itself do not affect the length; even for the empty message (one padded chunk) the output has 32 bytes.

Because $\texttt{hash256}(m) = \texttt{sha256}(\texttt{sha256}(m))$, and $\texttt{txid}$, $\texttt{wtxid}$, $\texttt{headerHash}$ are $\texttt{hash256}$ of various serializations, the statement entails that all of those also have 32 bytes; but the theorem does not state these consequences.

**What is not said.** Nothing is claimed about the *values* of the bytes: not that the function agrees with any standard SHA-256, not any test vector, not collision resistance or injectivity, not that different messages hash differently. It does not say that $\texttt{hash256}$, $\texttt{txid}$, $\texttt{headerHash}$ have length 32 by name. It says nothing about $\texttt{ripemd160}$ or $\texttt{sha1}$ or $\texttt{hash160}$ (the latter is the separate `hash160_length`). It does not state that the padded length is a multiple of 64 or that the number of chunks is $\lceil (|m| + 9)/64 \rceil$. It is purely the length of the final byte string, for every $m$.
