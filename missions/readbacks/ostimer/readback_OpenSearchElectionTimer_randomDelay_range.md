# Read-back: `OpenSearchElectionTimer.randomDelay_range`

## Notions used

**Draws.** A draw is an element $x$ of $\mathrm{Fin}(2^{64}) = \{0, \dots, 2^{64}-1\}$. The draw is read as the Java `long` $\mathrm{toLong}(x) = x - 2^{63}$, an order-preserving bijection onto $[-2^{63}, 2^{63}-1]$.

**`nonNegative`.** $\mathrm{nonNegative}(n) = 0$ if $n = -2^{63}$, and $|n|$ otherwise. It is a natural number.

**`randomDelay`.** For $M \in \mathbb{N}$:
$$\mathrm{randomDelay}(M, x) = \big(\mathrm{nonNegative}(x - 2^{63}) \bmod M\big) + 1 .$$
The remainder is the natural-number remainder, with Lean's convention $a \bmod 0 = a$. This transcribes Java's `toPositiveLongAtMost(randomNumber, upperBound) = nonNegative(randomNumber) % upperBound + 1` (ESF:169-172), applied to the draw.

## 1. Declaration

```lean
theorem OpenSearchElectionTimer.randomDelay_range (M : Nat) (hM : 1 ≤ M) (x : Fin (2 ^ 64)) :
    1 ≤ randomDelay M x ∧ randomDelay M x ≤ M
```

**Binders and hypotheses, in order:**
- $M \in \mathbb{N}$;
- $hM : 1 \le M$;
- $x \in \mathrm{Fin}(2^{64})$, any of the $2^{64}$ draws.

**Conclusion** (in $\mathbb{N}$):
$$1 \le \mathrm{randomDelay}(M, x) \;\wedge\; \mathrm{randomDelay}(M, x) \le M,$$
that is,
$$1 \le \big(\mathrm{nonNegative}(x - 2^{63}) \bmod M\big) + 1 \le M .$$

## 2. What is not constrained

- **No upper bound on $M$.** Values above $2^{63}-1$, beyond any Java `long`, are allowed. For $M > 2^{63}$ the conclusion still holds, but the values reach at most $2^{63}$, so $[1, M]$ is not filled.
- **Pointwise only.** The statement covers each draw $x$ separately. It says nothing about how often each value occurs (see `randomDelay_card` and `randomDelay_near_uniform`), and it does not claim that every value in $[1, M]$ is attained.
- **$hM$ is necessary.** For $M = 0$, Lean gives $\mathrm{randomDelay}(0, x) = \mathrm{nonNegative}(x - 2^{63}) + 1 \ge 1 > 0$, so the second conjunct fails. Java excludes $M = 0$ with an assertion.
- **Satisfiable, not vacuous.** The hypothesis holds for example with $M = 1$.
- **Covers every Java `long`.** `toLong` is a bijection onto the `long` range, so "for every $x$" amounts to "for every value `random.nextLong()` could return". This is a statement about the Lean function. The link to Java is the transcription, which matches ESF:169-172 for $M \ge 1$.

## 3. Plain-language summary

For any bound $M \ge 1$ and every possible 64-bit draw, the random part of an election attempt's delay is at least $1$ and at most $M$. This matches the range "(0, upperBound]" documented on the Java method `toPositiveLongAtMost`. The theorem says nothing about the distribution of the delay.
