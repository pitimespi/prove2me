# Read-back: `OpenSearchPreVote.maxDelay_schedule`

## Notions used

**Scheduler settings.** A settings value $s$ is four natural numbers: $\mathrm{initialTimeout}$, $\mathrm{backoffTime}$, $\mathrm{maxTimeout}$ and $\mathrm{duration}$ (milliseconds, per the docstring). $\mathrm{Valid}(s)$ is the conjunction:
- $1 \le \mathrm{initialTimeout} \le 10000$;
- $1 \le \mathrm{backoffTime} \le 60000$;
- $200 \le \mathrm{maxTimeout} \le 300000$;
- $\mathrm{initialTimeout} \le \mathrm{maxTimeout}$;
- $1 \le \mathrm{duration} \le 300000$.

**Delay bound.** $\mathrm{maxDelay}(s, k) = \min(s.\mathrm{maxTimeout},\ s.\mathrm{initialTimeout} + k\cdot s.\mathrm{backoffTime})$, in natural-number arithmetic.

## 1. Declaration

**Binders and hypothesis.**
- $s$: scheduler settings;
- $hs$: $\mathrm{Valid}(s)$.

**Conclusion.** Four conjuncts:
1. $\mathrm{maxDelay}(s, 0) = s.\mathrm{initialTimeout}$.
2. $\forall k\, k',\ k \le k' \rightarrow \mathrm{maxDelay}(s, k) \le \mathrm{maxDelay}(s, k')$: the bound is monotone in the attempt index.
3. $\forall k,\ \mathrm{maxDelay}(s, k) < s.\mathrm{maxTimeout} \rightarrow \big(\mathrm{maxDelay}(s, k+1) = \mathrm{maxDelay}(s, k) + s.\mathrm{backoffTime} \;\vee\; \mathrm{maxDelay}(s, k+1) = s.\mathrm{maxTimeout}\big)$. While below the cap, the next bound is one back-off step larger or equals the cap.
4. $\forall k,\ s.\mathrm{maxTimeout} \le k \rightarrow \mathrm{maxDelay}(s, k) = s.\mathrm{maxTimeout}$. For every attempt index at least $\mathrm{maxTimeout}$, the bound equals the cap.

## 2. What is not constrained

- **Conjunct 4 is loose.** It compares an attempt *index* $k$ with the millisecond *value* $\mathrm{maxTimeout}$. It is true because $\mathrm{backoffTime} \ge 1$ gives $k \cdot \mathrm{backoffTime} \ge k$.
  - The real saturation point is earlier: the first $k$ with $\mathrm{initialTimeout} + k\cdot\mathrm{backoffTime} \ge \mathrm{maxTimeout}$, that is, $k = \lceil (\mathrm{maxTimeout} - \mathrm{initialTimeout})/\mathrm{backoffTime}\rceil$.
  - With the defaults ($100$, $100$, $10000$) the bound first reaches $10000$ at $k = 99$, which I checked by evaluation. Conjunct 4 asserts saturation only from $k = 10000$.
  - Conjuncts 2 and 4 together do imply $\mathrm{maxDelay}(s, k) \le \mathrm{maxTimeout}$ for every $k$.
- **Conjunct 3 is a disjunction.** It does not say which alternative holds. Read alone, it would allow a jump straight to $\mathrm{maxTimeout}$ even when one back-off step would stay below the cap. The exact value, $\min(\mathrm{maxTimeout}, \mathrm{maxDelay}(s, k) + \mathrm{backoffTime})$, comes from the definition and is not stated. When $\mathrm{maxDelay}(s, k) + \mathrm{backoffTime} = \mathrm{maxTimeout}$, both alternatives hold.
- **Which parts of $\mathrm{Valid}$ matter.** As far as I can see:
  - conjunct 1 needs only $\mathrm{initialTimeout} \le \mathrm{maxTimeout}$;
  - conjunct 4 needs only $\mathrm{backoffTime} \ge 1$;
  - conjuncts 2 and 3 hold for all settings.

  The numeric bounds of $\mathrm{Valid}$ and the field $\mathrm{duration}$ play no role.
- **What is not stated.** Nothing is said about the actual (random) delays, only about their bound $\mathrm{maxDelay}$.
- **Vacuity.** None. $\mathrm{Valid}$ is satisfiable, for example by the defaults $\langle 100, 100, 10000, 500\rangle$.

## 3. Plain-language summary

For valid scheduler settings, the per-attempt delay bound starts at the initial timeout and never decreases. While it is below the maximum timeout, each attempt raises it by exactly the back-off time or brings it to the maximum. It equals the maximum timeout for every attempt index at least as large as the maximum timeout's numeric value, which is a loose saturation bound compared with where the cap is actually reached.
