# Read-back: `OpenSearchPreVote.nonNegative_two_to_one`

## Notions used

**$\mathrm{nonNegative}$.** For any integer $n$,
$$\mathrm{nonNegative}(n) = \begin{cases} 0 & \text{if } n = -2^{63},\\ |n| \in \mathbb{N} & \text{otherwise.}\end{cases}$$
The Lean text `-2 ^ 63` parses as $-(2^{63}) = -9223372036854775808$, which is Java's `Long.MIN_VALUE`. I confirmed the parse with `pp.parens`; $(-2)^{63}$ would give the same value anyway, since $63$ is odd.

## 1. Declaration

**Binders and hypotheses.**
- $v \in \mathbb{N}$;
- $hv$: $v < 2^{63}$;
- $n \in \mathbb{Z}$;
- $hn$: $-2^{63} \le n \wedge n < 2^{63}$, that is, $n$ is in Java's long range.

**Conclusion.**
$$\mathrm{nonNegative}(n) = v \iff n = v \;\vee\; n = \begin{cases} -2^{63} & \text{if } v = 0,\\ -v & \text{if } v \neq 0.\end{cases}$$
Here $v$ on the right is cast to an integer.

Unfolded:
- For $v = 0$, the longs mapped to $0$ are exactly $0$ and $-2^{63}$.
- For $0 < v < 2^{63}$, the longs mapped to $v$ are exactly $v$ and $-v$.

In both cases the two candidates are distinct and lie in $[-2^{63}, 2^{63})$. So every value in $[0, 2^{63})$ has exactly two preimages among the longs, and $\mathrm{nonNegative}$ is exactly two-to-one from the longs onto $[0, 2^{63})$. That the candidates lie in range is elementary arithmetic and is not itself part of the statement.

## 2. What is not constrained

- **Integers outside the long range.** $hn$ excludes them, so nothing is said about them. There $\mathrm{nonNegative}$ is just $|n|$, so the preimage sets differ. For example, $\mathrm{nonNegative}(-2^{63} - 1) = \mathrm{nonNegative}(2^{63} + 1) = 2^{63} + 1$, which I checked by evaluation.
- **Values $v \ge 2^{63}$.** $hv$ excludes them. The theorem does not state that no long maps to such a value, although that is true by the definition.
- **What is not stated.** Nothing is said about $\mathrm{toPositiveLongAtMost}$ or about the uniformity of the derived delays, for example the bias introduced by $\bmod$ when the bound does not divide $2^{63}$.
- **Vacuity.** None. Both hypotheses are satisfiable, for example with $v = 0$ and $n = 0$.

## 3. Plain-language summary

Restricted to Java long values, $\mathrm{nonNegative}$ sends exactly $v$ and $-v$ to each $v$ with $0 < v < 2^{63}$, and exactly $0$ and `Long.MIN_VALUE` to $0$. Each value in $[0, 2^{63})$ therefore has exactly two long preimages.
