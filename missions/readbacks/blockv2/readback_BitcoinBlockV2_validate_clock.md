# Read-back: `BitcoinBlockV2.validate_clock`

**Binders.** $S$ is a chain state (a list of headers and a ledger); $b$ is a block; $\mathit{now}$ and $\mathit{now}'$ are integers.

**Hypotheses.**
- $h$: $\mathrm{validate}(S, b, \mathit{now}) \ne \mathrm{futureTime}$.
- $h_{le}$: $\mathit{now} \le \mathit{now}'$.

**Conclusion.** $\mathrm{validate}(S, b, \mathit{now}') = \mathrm{validate}(S, b, \mathit{now})$: the outcomes (one of $\mathrm{accept}(S', \mathit{undo})$ with its full payload, $\mathrm{invalid}$, $\mathrm{futureTime}$, $\mathrm{missingPrev}$) coincide.

Unfolding $\mathrm{validate}(S, b, t)$: first $\mathrm{acceptHeader}(S, b.\mathit{header}, t)$, which returns, in order, $\mathrm{invalid}$ if the header's proof of work fails (compact bits $\bmod 2^{32}$ do not decode or the little-endian header hash exceeds the decoded target); $\mathrm{missingPrev}$ if $b.\mathit{header}.\mathit{prevBlock} \ne S.\mathrm{tipHash}$; $\mathrm{invalid}$ if the bits differ from $S.\mathrm{requiredBits}$; $\mathrm{invalid}$ if $\mathit{time} \le S.\mathit{mtp}$; $\mathrm{futureTime}$ if $t + 7200 < \mathit{time}$; $\mathrm{invalid}$ if the version is outdated for $S.\mathrm{tipHeight}$; else accept. When the header is accepted: $\mathrm{invalid}$ unless $\mathrm{checkBlock}(b)$; $\mathrm{invalid}$ unless $\mathrm{contextualCheckBlock}(S, b)$; $\mathrm{invalid}$ unless $\mathrm{connectBlock}(S, b) = \mathrm{some}(u, \mathit{undo})$; and then $\mathrm{accept}((S.\mathit{headers} \mathbin{+\!\!+} [b.\mathit{header}], u), \mathit{undo})$. The clock $t$ is consulted only in the test $t + 7200 < \mathit{time}$; no other part of the computation depends on it.

**Edge cases silently included:** $\mathit{now}' = \mathit{now}$ (trivial); the hypothesis $h$ is satisfied by every rejection for a reason checked before the clock (bad proof of work, wrong previous hash, wrong bits, time not above the median) as well as by every outcome after the clock test; negative clocks are allowed.
