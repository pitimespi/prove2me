# Read-back: `BitcoinBlock.validate_clock`

## Binders and hypotheses

- $S$ : a chain state; $b$ : a serialized block.
- $\mathit{now}, \mathit{now}' \in \mathbb{Z}$ : two clock values.
- Hypothesis $h$ : $\mathrm{validate}(S, b, \mathit{now}) \ne \mathrm{futureTime}$.
- Hypothesis $h_{le}$ : $\mathit{now} \le \mathit{now}'$.

## Conclusion

$$\mathrm{validate}(S, b, \mathit{now}') = \mathrm{validate}(S, b, \mathit{now}),$$
an equality in the outcome type (accept with a state and an undo list / invalid / futureTime / missingPrev).

### Unfolding

$\mathrm{validate}(S,b,t)$ evaluates $\mathrm{acceptHeader}(S, b.\mathrm{header}, t)$, the ordered chain: invalid if the header fails proof of work; missingPrev if $b.\mathrm{header.prevBlock} \ne \mathrm{tipHash}(S)$; invalid if the bits modulo $2^{32}$ differ from $\mathrm{requiredBits}(S)$; invalid if $b.\mathrm{header.time} \le \mathrm{mtp}(S)$; **futureTime if $t + 7200 < b.\mathrm{header.time}$**; invalid if the version is outdated for $\mathrm{tipHeight}+1$; else accept. If the header outcome is not accept it is returned; otherwise the clock-independent checks $\mathrm{checkBlock}(b)$, $\mathrm{contextualCheckBlock}(S,b)$ and $\mathrm{connectBlock}(S,b)$ determine invalid or $\mathrm{accept}(\langle S.\mathrm{headers}\mathbin{+\!\!+}[b.\mathrm{header}], u\rangle, \mathit{undo})$.

The clock enters only through the single test $t + 7200 < b.\mathrm{header.time}$. Hypothesis $h$ says that at clock $\mathit{now}$ the result is not futureTime: either an earlier test already fired (in which case the clock is never consulted), or $b.\mathrm{header.time} \le \mathit{now} + 7200$. The conclusion asserts that at any clock $\mathit{now}' \ge \mathit{now}$ the outcome, including the payload of an accept, is the same.

## Edge cases silently included

$\mathit{now}' = \mathit{now}$ (trivial); $h$ satisfied because of an earlier failure (proof of work, parent, bits, median time), where the clock is irrelevant; $b.\mathrm{header.time}$ unbounded natural; no well-formedness of $S$ or $b$ assumed.
