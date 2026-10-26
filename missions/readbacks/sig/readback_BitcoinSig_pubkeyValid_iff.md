# Read-back: `BitcoinSig.pubkeyValid_iff`

**Binders and hypothesis.** Universally quantified over a byte string $pk$. No hypotheses.

**Conclusion.** `pubkeyValid` $pk$ = true if and only if
$$\big(|pk| = 33 \ \land\ (pk[0] = 2 \lor pk[0] = 3)\big)\ \lor\ \big(|pk| = 65 \ \land\ (pk[0] = 4 \lor pk[0] = 6 \lor pk[0] = 7)\big),$$
where $pk[0]$ denotes the numeric value of the first byte, taken to be $0$ if $pk$ is empty (the "get with default $0$" accessor). In the right side the length conjuncts make the empty case irrelevant: an empty string has length $0$, so neither disjunct can hold.

**Unfolding the left side.** `pubkeyValid` $pk$ is: false if $pk$ is empty; otherwise, with $h$ the first byte, the Boolean decision of `pubkeyLen` $h$ $= |pk|$, where `pubkeyLen` $h$ is $33$ if $h \in \{2,3\}$, $65$ if $h \in \{4,6,7\}$, and $0$ for every other header value. Since a non-empty string has positive length, the "$0$" case can never equal $|pk|$, so validity amounts to: header $2$ or $3$ with length exactly $33$, or header $4$, $6$ or $7$ with length exactly $65$. That is precisely the right side; the biconditional is a direct restatement of the definition with the default-accessor phrasing.

**Edge cases.** A 33-byte string starting with `0x04` is not valid; a 65-byte string starting with `0x02` is not valid; a string starting with any byte outside $\{2,3,4,6,7\}$ is never valid regardless of length; the hybrid headers `0x06`/`0x07` *are* accepted at length 65.

**What is not said.** The statement does not say anything about whether the remaining bytes encode a point on the curve, whether the abscissa is below the field prime, or whether the parity announced by the header is consistent with the ordinate — `pubkeyValid` is a header/length test only, and the biconditional faithfully says no more. It does not relate `pubkeyValid` to `parsePubkey`, to `isCompressedOrUncompressedPubKey` (which rejects headers 6 and 7), or to `isCompressedPubKey`. It does not say anything about the flags or the encoding checks. It does not say that the right side is decidable or exclusive (the two disjuncts are in fact mutually exclusive by length, but that is not asserted).
