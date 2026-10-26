We prove the acceptance condition of `CheckProofOfWorkImpl`: for every hash $h$ and word $c$,
$$\mathrm{checkProofOfWork}(h, c) = \mathtt{true} \iff \neg\mathrm{negative}(c) \wedge \neg\mathrm{overflow}(c) \wedge 0 < \mathrm{specTarget}(c) \wedge \mathrm{specTarget}(c) \le 2^{224}-1 \wedge h \le \mathrm{specTarget}(c).$$

**Idea.** `DeriveTarget` rejects when any of four Boolean tests fires — negative, decoded value zero, overflow, decoded value above the limit — and otherwise returns the decoded value, which `BitcoinPow.setCompact_eq_spec` identifies with the exact value once the overflow test is known to be clear.

**Step 1 (some test fires).** Then the check returns false. If the right-hand side held, the negative and overflow flags would be clear, the decoded value would equal the exact value, and the remaining two tests (zero, above limit) would contradict $0 < \mathrm{specTarget}(c) \le \mathrm{powLimit}$.

**Step 2 (no test fires).** The flags are clear, so the decoded value is the exact value; it is nonzero and at most the limit; and the check reduces to $h \le \mathrm{specTarget}(c)$, which is the last conjunct.
