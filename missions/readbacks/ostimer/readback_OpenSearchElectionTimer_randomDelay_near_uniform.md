# Read-back: `OpenSearchElectionTimer.randomDelay_near_uniform`

## Notions used

**Draws.** A draw is an element $x$ of $\mathrm{Fin}(2^{64})$, read as the Java `long` $\mathrm{toLong}(x) = x - 2^{63}$.

**`nonNegative`.** $\mathrm{nonNegative}(n) = 0$ if $n = -2^{63}$, and $|n|$ otherwise.

**`randomDelay`.** $\mathrm{randomDelay}(M, x) = (\mathrm{nonNegative}(x - 2^{63}) \bmod M) + 1$, with the natural-number remainder (and $a \bmod 0 = a$).

**Notation.** For $1 \le d \le M$, write $N_d = \#\{x \in \mathrm{Fin}(2^{64}) : \mathrm{randomDelay}(M, x) = d\}$. $\lfloor a/b \rfloor$ is natural-number floor division, which is $0$ when $b = 0$.

## 1. Declaration

```lean
theorem OpenSearchElectionTimer.randomDelay_near_uniform (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    2 * (2 ^ 63 / M) ≤ (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card ∧
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card ≤ 2 * ((2 ^ 63 + M - 1) / M)
```

**Binders:** $M, d \in \mathbb{N}$.

**Hypotheses, in order:**
- $hM : 1 \le M$;
- $hM' : M \le 2^{63}$;
- $hd : 1 \le d$;
- $hdM : d \le M$.

**Conclusion** (in $\mathbb{N}$):
$$2\left\lfloor \frac{2^{63}}{M} \right\rfloor \;\le\; N_d \;\le\; 2\left\lfloor \frac{2^{63} + M - 1}{M} \right\rfloor = 2\left\lceil \frac{2^{63}}{M}\right\rceil .$$
The last equality uses $M \ge 1$.

**Probability form.** Dividing by $2^{64}$:
$$\frac{\lfloor 2^{63}/M\rfloor}{2^{63}} \le \Pr[\mathrm{randomDelay}(M, x) = d] \le \frac{\lceil 2^{63}/M\rceil}{2^{63}} .$$
This interval contains $1/M$ and has width at most $1/2^{63}$. The width is $0$ exactly when $M$ divides $2^{63}$, in which case the delay is exactly uniform.

## 2. What is not constrained

- **Weaker than `randomDelay_card`.** That theorem gives $N_d = 2(\lfloor (2^{63}-d)/M \rfloor + 1)$ exactly. Since $2^{63} \le 2^{63} - d + M \le 2^{63} + M - 1$, the present interval follows from it.
- **$hd$ and $hdM$ are needed for the lower bound.** For $d \notin [1, M]$ we have $N_d = 0$, while $2\lfloor 2^{63}/M\rfloor > 0$ when $M \le 2^{63}$.
- **$hM'$ is not needed for truth.** For $M > 2^{63}$:
  - $\lfloor 2^{63}/M \rfloor = 0$, so the lower bound is trivial;
  - $N_d \in \{0, 2\}$;
  - $2\lfloor (2^{63}+M-1)/M\rfloor = 2$, so the upper bound still holds.
- **$hM$ is redundant.** It follows from $hd$ and $hdM$.
- **Idealization.** As in the card theorem, the count is over all $2^{64}$ draws (a uniform 64-bit idealization), not over the $2^{48}$ values the real `java.util.Random.nextLong()` can produce.
- **Satisfiable, not vacuous.**

## 3. Plain-language summary

For a bound $M$ with $1 \le M \le 2^{63}$, each delay value $d \in [1, M]$ is produced by at least $2\lfloor 2^{63}/M\rfloor$ and at most $2\lceil 2^{63}/M\rceil$ of the $2^{64}$ draws. So under a uniform 64-bit draw, its probability is within $1/2^{63}$ of $1/M$. Delays drawn this way are uniform on $[1, M]$ up to that rounding.
