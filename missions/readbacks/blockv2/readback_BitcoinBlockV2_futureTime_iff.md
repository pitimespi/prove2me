# Read-back: `BitcoinBlockV2.futureTime_iff`

**Binders.** $S$ is a chain state (a list of headers and a ledger); $b$ is a block; $\mathit{now}$ is an integer. No hypotheses.

**Conclusion.** $\mathrm{validate}(S, b, \mathit{now}) = \mathrm{futureTime}$ if and only if all of the following hold:
1. $\mathrm{checkHeaderPow}(b.\mathit{header}) = \mathrm{true}$ — the 32-bit word $c = b.\mathit{header}.\mathit{bits} \bmod 2^{32}$ decodes (`deriveTarget`: not negative, non-zero, not overflowing, decoded value $t \le 2^{224}-1$, with the decoding truncated modulo $2^{256}$) and the little-endian integer value of $\mathrm{hash256}$ of the serialized header is $\le t$;
2. $b.\mathit{header}.\mathit{prevBlock} = S.\mathrm{tipHash}$, the hash of the last header of $S.\mathit{headers}$ (genesis header if empty);
3. $c = S.\mathrm{requiredBits}$ as 32-bit words, where $S.\mathrm{requiredBits}$ is the tip's bits unless $(S.\mathrm{tipHeight}+1) \bmod 2016 = 0$, in which case the retargeted word computed from the tip's bits and time and the time of the header at index $S.\mathrm{tipHeight} \mathbin{\dot-} 2015$;
4. $S.\mathit{mtp} < b.\mathit{header}.\mathit{time}$ (the header time as an integer exceeds the tip's median time past: index $\lfloor\ell/2\rfloor$ of the ascending sort of the most recent $\le 11$ header times, $0$ for an empty list);
5. $\mathit{now} + 7200 < b.\mathit{header}.\mathit{time}$.

Unfolding the left side: $\mathrm{validate}$ returns $\mathrm{futureTime}$ exactly when $\mathrm{acceptHeader}(S, b.\mathit{header}, \mathit{now})$ returns $\mathrm{futureTime}$ (the block-level checks are never reached and the post-header path never produces $\mathrm{futureTime}$), and $\mathrm{acceptHeader}$ returns $\mathrm{futureTime}$ exactly when, in order, proof of work holds, the previous-block hash matches the tip, the bits match the required bits, the time exceeds the median time past, and then $\mathit{now} + 7200 < \mathit{time}$; the version-outdated test is only reached when the future-time test fails, so the version does not appear in the right side.

**Edge cases silently included:** empty header list (tip defaults to the genesis header, median $0$, tip height $0$); nothing about $b.\mathit{vtx}$ is constrained; the version of the header is unconstrained.
