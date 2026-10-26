# Read-back: `BitcoinVerify.isPayToScriptHash_iff`

**Binders and hypothesis.** There is one universally quantified variable: $s$, a byte string (a finite list of 8-bit bytes). There are no hypotheses.

**Conclusion.** The statement is a biconditional:

$$\mathrm{isPayToScriptHash}(s) = \mathrm{true} \iff \exists h \text{ (a byte string)},\ |h| = 20 \ \wedge\ s = \mathrm{p2shBytes}(h).$$

**Unfolding the left-hand side.** `isPayToScriptHash s` is a Boolean computed as the conjunction of four decidable tests: $|s| = 23$; the byte at index $0$ of $s$ equals $\mathtt{0xa9}$; the byte at index $1$ equals $\mathtt{0x14}$; the byte at index $22$ equals $\mathtt{0x87}$. Indices are read with a default of $0$ when out of range, but because the length test forces $|s| = 23$, all three indices are in range whenever the whole conjunction is true. The 20 bytes at indices $2, \ldots, 21$ are unconstrained. So the left side says exactly: $s$ is a 23-byte string of the form $\mathtt{0xa9}\ \mathtt{0x14}\ b_2 \cdots b_{21}\ \mathtt{0x87}$.

**Unfolding the right-hand side.** `p2shBytes h` is the byte string $[\mathtt{0xa9}] \,\|\, \mathrm{pushBytes}(h) \,\|\, [\mathtt{0x87}]$, where `pushBytes` is the canonical push encoding: for $|h| < 76$ it is the single length byte $|h|$ followed by $h$. With $|h| = 20$ this is the 23-byte string $\mathtt{0xa9}\ \mathtt{0x14}\ h\ \mathtt{0x87}$. So the right side says exactly: there is a 20-byte string $h$ with $s = \mathtt{0xa9}\ \mathtt{0x14}\ h\ \mathtt{0x87}$.

**Logical content.** The theorem asserts that the two syntactic characterizations coincide for every byte string $s$: the index-wise test with a fixed length is equivalent to the existence of a 20-byte middle segment. Both directions are claimed. The existential is a plain existence, not uniqueness, though with $s$ fixed the only candidate is $s_2 \ldots s_{21}$.

**What is not said.** The theorem says nothing about the behaviour of `verifyScript` or of any evaluation on such an $s$; it does not say that a P2SH script is or is not a witness program; it does not say anything about `p2shBytes h` for $|h| \ne 20$ (such strings exist and may or may not satisfy `isPayToScriptHash` — the theorem only asserts that if `isPayToScriptHash s` holds then *some* 20-byte $h$ works, and conversely); it does not mention hashes, so the middle 20 bytes are not required to be the `hash160` of anything; and it does not relate `isPayToScriptHash` to any flag in a context.
