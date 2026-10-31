# Read-back: `OpenSearchElectionTimer.default_example`

## Notions used

**`contestedBound`.**
$$\mathrm{contestedBound}(n, \delta, M_{\min}) = \frac{\binom{n}{2}\,(2\delta \mathbin{\dot-} 1)\,\lfloor (2^{63} + M_{\min} - 1)/M_{\min}\rfloor}{2^{63}} \in \mathbb{Q},$$
with truncated natural subtraction and natural floor division, cast to $\mathbb{Q}$. For $\delta, M_{\min} \ge 1$ this is $\binom{n}{2}(2\delta-1)\lceil 2^{63}/M_{\min}\rceil / 2^{63}$.

**Related theorems.** Under hypotheses, `contested_prob_le` shows this number bounds the probability that one round of $n$ timers is contested with margin $\delta$, when every bound is at least $M_{\min}$. `all_contested_prob_le` shows that its $K$-th power bounds the probability that $K$ causally chosen rounds are all contested. The present theorem does not invoke either of them.

## 1. Declaration

```lean
theorem OpenSearchElectionTimer.default_example :
    contestedBound 3 100 10000 < 6 / 100 ∧ contestedBound 3 100 10000 ^ 5 < 1 / 1000000
```

**Binders and hypotheses:** none.

**Conclusion** (in $\mathbb{Q}$). Because `contestedBound` returns $\mathbb{Q}$, the numerals `6 / 100` and `1 / 1000000` are rational divisions, not natural-number divisions (which would give $0$). The theorem asserts
$$\mathrm{contestedBound}(3, 100, 10000) < \tfrac{6}{100} \;\wedge\; \mathrm{contestedBound}(3, 100, 10000)^5 < \tfrac{1}{1000000}.$$

**Unfolded:**
$$\mathrm{contestedBound}(3, 100, 10000) = \frac{3 \cdot 199 \cdot \lfloor (2^{63} + 9999)/10000\rfloor}{2^{63}} = \frac{597 \cdot 922337203685478}{2^{63}} = \frac{275317655300115183}{2^{62}} \approx 0.0597000000000000271 .$$
Here $\lceil 2^{63}/10000\rceil = 922337203685478$, since $2^{63} \bmod 10000 = 5808$. The fifth power is $\approx 7.5835 \times 10^{-7}$. I checked both conjuncts with exact rational arithmetic: the margins are $0.06 - 0.0597\ldots \approx 3.0 \times 10^{-4}$ and $10^{-6} - 7.58\ldots \times 10^{-7} \approx 2.4 \times 10^{-7}$.

## 2. What is not constrained

- **Pure arithmetic.** The statement is about specific numbers. It involves no draws, no probability, no offsets, no bounds and no scheduler.
- **The parameters are literals.**
  - $n = 3$: candidates.
  - $\delta = 100$: the margin.
  - $M_{\min} = 10000$: the minimum bound.
  - $5$: the number of rounds, if read through `all_contested_prob_le` with $K = 5$.
- **No link to the default settings in Lean.** $10000$ coincides with `SchedulerSettings.default.maxTimeout`, but the statement does not mention `SchedulerSettings.default` or `maxDelay`. With the default settings, $\mathrm{maxDelay}(\mathrm{default}, k) = \min(10000,\ 100 + 100k)$ reaches $10000$ only from attempt index $k = 99$ (the 100th attempt). Applying `contested_prob_le` with $M_{\min} = 10000$ requires every bound in the round to be at least $10000$. For earlier attempts the same $n$ and $\delta$ give weaker or trivial bounds: $\mathrm{contestedBound}(3, 100, 1000) \approx 0.597$, and $\mathrm{contestedBound}(3, 100, 100) = 5.97$, which is vacuous as a probability bound. The value is at least $1$ exactly when $1 \le M_{\min} \le 597$.
- **$\delta = 100$ is not justified by any Lean term.** Nothing shows that a 100 ms margin lets an uncontested candidate's pre-voting round and election finish before the others start.
- **The name overstates the content.** "default_example" suggests the default configuration. The Lean statement only establishes the two numerical inequalities.
- **No hypotheses**, so nothing is vacuous. The statement is a closed numerical claim and, by my computation, true.

## 3. Plain-language summary

For 3 candidates, a margin of 100 and a minimum bound of 10000, the per-round contested bound $\mathrm{contestedBound}$ is about $5.97\%$, below $6\%$. Its fifth power is about $7.6 \times 10^{-7}$, below one in a million. Only when combined with `contested_prob_le` and `all_contested_prob_le` (not by this theorem itself) do these numbers bound the chance of a contested round, or of five consecutive contested rounds, and only for rounds in which every candidate's bound is at least 10000.
