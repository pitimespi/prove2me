# Read-back: `BitcoinBlock.futureTime_transient`

## Binders and hypotheses

- $S$ : a chain state; $b$ : a serialized block; $\mathit{now} \in \mathbb{Z}$.
- Hypothesis $h$ : $\mathrm{validate}(S, b, \mathit{now}) = \mathrm{futureTime}$.
- $\mathit{now}' \in \mathbb{Z}$ : a second clock value.
- Hypothesis $h_{le}$ : $b.\mathrm{header.time} \le \mathit{now}' + 7200$ (time cast to $\mathbb{Z}$; $7200$ = `MAX_FUTURE_BLOCK_TIME`).

## Conclusion

A conjunction of two claims:

1. $\mathrm{validate}(S, b, \mathit{now}') \ne \mathrm{futureTime}$;
2. $\mathrm{validate}(S, b, \mathit{now}') = \mathrm{validate}\big(S, b, b.\mathrm{header.time} - 7200\big)$, an equality of outcomes (the four-constructor type accept/invalid/futureTime/missingPrev, where accept carries a state and an undo list, so equality of accept outcomes includes equality of those payloads).

### What $h$ says

By the structure of $\mathrm{validate}$ (it returns the header outcome unchanged unless that is accept), $h$ holds exactly when the header passes proof-of-work, has $\mathrm{prevBlock}$ equal to the tip hash of $S$, has bits (modulo $2^{32}$) equal to the required bits of $S$, has time strictly above the tip's median-time-past, and $\mathit{now} + 7200 < b.\mathrm{header.time}$.

### What the conclusion says, unfolded

$\mathrm{validate}(S,b,t)$ depends on the clock $t$ only in the single test "$t + 7200 < b.\mathrm{header.time}$" of $\mathrm{acceptHeader}$, which yields futureTime when true. With the clock $t = b.\mathrm{header.time} - 7200$ that test reads $b.\mathrm{header.time} < b.\mathrm{header.time}$, which is false. With the clock $\mathit{now}'$, under $h_{le}$ the test is false as well. In both cases evaluation continues with the version-floor test (invalid if the version is below $2$, $3$ or $4$ while $227931$, $363725$ or $388381$ respectively is $\le \mathrm{tipHeight}+1$), then $\mathrm{checkBlock}(b)$ (invalid if false), $\mathrm{contextualCheckBlock}(S,b)$ (invalid if false), then $\mathrm{connectBlock}(S,b)$ (invalid if none, else $\mathrm{accept}(\langle S.\mathrm{headers} \mathbin{+\!\!+} [b.\mathrm{header}], u\rangle, \mathit{undo})$). Claim 1 asserts the outcome at clock $\mathit{now}'$ is not futureTime; claim 2 asserts it coincides with the outcome at the boundary clock $b.\mathrm{header.time} - 7200$.

## Edge cases silently included

$h$ and $h_{le}$ together force $\mathit{now} < \mathit{now}'$ but no such hypothesis is stated; $\mathit{now}'$ may be far in the future; the block's transactions enter only through the later checks; $b.\mathrm{header.time}$ is an unbounded natural cast to $\mathbb{Z}$, so $b.\mathrm{header.time} - 7200$ may be negative; if $h$ is unsatisfiable for the given $S$ and $b$ the statement is vacuous.
