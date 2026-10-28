# Read-back: `BitcoinBlockV2.futureTime_transient`

**Binders.** $S$ is a chain state; $b$ is a block; $\mathit{now}$ and $\mathit{now}'$ are integers.

**Hypotheses.**
- $h$: $\mathrm{validate}(S, b, \mathit{now}) = \mathrm{futureTime}$. Unfolding, this holds exactly when $\mathrm{acceptHeader}(S, b.\mathit{header}, \mathit{now}) = \mathrm{futureTime}$, i.e. proof of work holds for the header, $b.\mathit{header}.\mathit{prevBlock} = S.\mathrm{tipHash}$, $b.\mathit{header}.\mathit{bits} \bmod 2^{32} = S.\mathrm{requiredBits}$, $S.\mathit{mtp} < \mathit{time}$, and $\mathit{now} + 7200 < \mathit{time}$, where $\mathit{time} = b.\mathit{header}.\mathit{time}$ as an integer. The integer $\mathit{now}$ occurs only in this hypothesis.
- $h_{le}$: $\mathit{time} \le \mathit{now}' + 7200$ (the constant `MAX_FUTURE_BLOCK_TIME` is $7200$).

**Conclusion.** Two statements:
1. $\mathrm{validate}(S, b, \mathit{now}') \ne \mathrm{futureTime}$.
2. $\mathrm{validate}(S, b, \mathit{now}') = \mathrm{validate}(S, b, \mathit{time} - 7200)$ — validation at clock $\mathit{now}'$ gives the same outcome (same constructor and, for an accept, the same new state and undo list) as validation at the integer clock $\mathit{time} - 7200$.

Here $\mathrm{validate}(S, b, t)$ is: $\mathrm{acceptHeader}(S, b.\mathit{header}, t)$ (returning $\mathrm{invalid}$ for failed proof of work, $\mathrm{missingPrev}$ for a non-matching previous hash, $\mathrm{invalid}$ for wrong bits or time $\le$ median time past, $\mathrm{futureTime}$ when $t + 7200 < \mathit{time}$, $\mathrm{invalid}$ for an outdated version), and when that accepts: $\mathrm{invalid}$ unless $\mathrm{checkBlock}(b)$, unless $\mathrm{contextualCheckBlock}(S, b)$, unless $\mathrm{connectBlock}(S, b) = \mathrm{some}(u, \mathit{undo})$, in which case $\mathrm{accept}((S.\mathit{headers} \mathbin{+\!\!+} [b.\mathit{header}], u), \mathit{undo})$. The clock $t$ enters only through the single test $t + 7200 < \mathit{time}$.

**Edge cases silently included:** $\mathit{now}$ is unused apart from $h$; $\mathit{now}'$ may be smaller than $\mathit{now}$; $\mathit{time} - 7200$ may be negative (integer arithmetic); the second conclusion asserts equality of the full outcome including the accepted state.
