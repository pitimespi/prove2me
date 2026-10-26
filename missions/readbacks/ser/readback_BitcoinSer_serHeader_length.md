# Read-back: `BitcoinSer.serHeader_length`

**Binders and hypothesis.** A header record $h$ and one hypothesis $hw : h.\texttt{wf}$, which unfolds to the conjunction
$$-2^{31} \le h.\texttt{version} < 2^{31},\quad |h.\texttt{prevBlock}| = 32,\quad |h.\texttt{merkleRoot}| = 32,\quad h.\texttt{time} < 2^{32},\quad h.\texttt{bits} < 2^{32},\quad h.\texttt{nonce} < 2^{32}.$$
Here $h.\texttt{version}$ is an integer (signed), the two hash fields are byte strings of a priori unrestricted length, and time/bits/nonce are natural numbers.

**Conclusion.** The serialized header has exactly 80 bytes:
$$|\texttt{serHeader}(h)| = 80 .$$

**Unfolding.** $\texttt{serHeader}(h) = \texttt{serInt32}(h.\texttt{version}) \mathbin{+\!\!+} h.\texttt{prevBlock} \mathbin{+\!\!+} h.\texttt{merkleRoot} \mathbin{+\!\!+} \texttt{ser32}(h.\texttt{time}) \mathbin{+\!\!+} \texttt{ser32}(h.\texttt{bits}) \mathbin{+\!\!+} \texttt{ser32}(h.\texttt{nonce})$. The pieces have lengths $4$ (since $\texttt{serInt32}$ is $\texttt{leBytes}\;4$ of a reduced value, always 4 bytes), $|h.\texttt{prevBlock}|$, $|h.\texttt{merkleRoot}|$ (both emitted raw, with no length prefix), and $4, 4, 4$. So the length is $16 + |h.\texttt{prevBlock}| + |h.\texttt{merkleRoot}|$ for *any* header, and the theorem's content is exactly that under the two length conjuncts of $\texttt{wf}$ this is $16 + 32 + 32 = 80$.

Of the seven conjuncts of $h.\texttt{wf}$, only $|h.\texttt{prevBlock}| = 32$ and $|h.\texttt{merkleRoot}| = 32$ are relevant to the length; the range conditions on version, time, bits and nonce are assumed but play no role, because the fixed-width encoders produce 4 bytes regardless of the value (they truncate rather than grow). The hypothesis is thus stronger than what the conclusion needs; a reader might expect the statement to assume only the two length equalities.

**What is not said.** Nothing about headers that are not well-formed; in particular the theorem does not say that a header with hash fields of other lengths serializes to something other than 80 bytes (though by the formula it would). Nothing about the content of the bytes, the position of fields, byte order, or the readability of the serialization (that is `header_roundtrip`). Nothing about $\texttt{headerHash}$, blocks, or $\texttt{serBlock}$. The statement is a single length equality under the full $\texttt{wf}$ assumption.
