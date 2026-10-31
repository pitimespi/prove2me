# Read-back: `OpenSearchElectionTimer.contested_prob_le`

## Notions used

**Draws and delays.** A draw is an element of $\mathrm{Fin}(2^{64})$, read as the Java `long` $\mathrm{toLong}(x) = x - 2^{63}$. $\mathrm{nonNegative}(n)$ is $0$ if $n = -2^{63}$ and $|n|$ otherwise. $\mathrm{randomDelay}(M, x) = (\mathrm{nonNegative}(x - 2^{63}) \bmod M) + 1$, a natural number, which lies in $[1, M]$ for $M \ge 1$.

**Fire times.** Let $\mathrm{offset} : \mathrm{Fin}\,n \to \mathbb{Z}$, $\mathrm{bound} : \mathrm{Fin}\,n \to \mathbb{N}$ and a draw vector $x : \mathrm{Fin}\,n \to \mathrm{Fin}(2^{64})$. Candidate $i$ fires at
$$T_i = \mathrm{fireTime}(\mathrm{offset}, \mathrm{bound}, x, i) = \mathrm{offset}(i) + \mathrm{randomDelay}(\mathrm{bound}(i), x(i)) \in \mathbb{Z}.$$

**Uncontested.**
$$\mathrm{Uncontested}(\mathrm{offset}, \mathrm{bound}, \delta, x) \iff \exists i,\ \forall j \ne i,\ T_i + \delta \le T_j$$
(in $\mathbb{Z}$). Its negation is
$$\forall i\ \exists j \ne i,\ T_j < T_i + \delta .$$
For $\delta \ge 1$ and $n \ge 1$, the negation holds iff $n \ge 2$ and the two smallest fire times, counted with multiplicity, differ by less than $\delta$ (ties included). For $n = 1$, every draw is uncontested.

**`contestedBound`.**
$$\mathrm{contestedBound}(n, \delta, M_{\min}) = \frac{\binom{n}{2}\,(2\delta \mathbin{\dot-} 1)\,\lfloor (2^{63} + M_{\min} - 1)/M_{\min}\rfloor}{2^{63}} \in \mathbb{Q},$$
with natural-number truncated subtraction and floor division (where $a/0 = 0$). For $\delta, M_{\min} \ge 1$ this is $\binom{n}{2}(2\delta-1)\lceil 2^{63}/M_{\min}\rceil/2^{63}$.

## 1. Declaration

```lean
theorem OpenSearchElectionTimer.contested_prob_le (n δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin n → Int) (bound : Fin n → Nat) (hbound : ∀ i, Mmin ≤ bound i ∧ bound i ≤ 2 ^ 63) :
    ((Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card : ℚ) / (2 ^ 64) ^ n ≤
      contestedBound n δ Mmin
```

**Binders and hypotheses, in order:**
- $n, \delta, M_{\min} \in \mathbb{N}$;
- $hn : 1 \le n$;
- $h\delta : 1 \le \delta$;
- $hM : 1 \le M_{\min}$;
- $\mathrm{offset} : \mathrm{Fin}\,n \to \mathbb{Z}$;
- $\mathrm{bound} : \mathrm{Fin}\,n \to \mathbb{N}$;
- $hbound : \forall i,\ M_{\min} \le \mathrm{bound}(i) \le 2^{63}$.

**Conclusion** (in $\mathbb{Q}$). Here $x$ ranges over all $(2^{64})^n$ functions $\mathrm{Fin}\,n \to \mathrm{Fin}(2^{64})$:
$$\frac{\#\{x : \neg\,\mathrm{Uncontested}(\mathrm{offset}, \mathrm{bound}, \delta, x)\}}{(2^{64})^n} \;\le\; \binom{n}{2}\cdot\frac{(2\delta - 1)\,\lceil 2^{63}/M_{\min}\rceil}{2^{63}} .$$

**Probability reading.** The draws $x(0), \dots, x(n-1)$ are independent and uniform on $\mathrm{Fin}(2^{64})$. The probability that no candidate fires at least $\delta$ before all the others is at most $\binom{n}{2}(2\delta-1)\lceil 2^{63}/M_{\min}\rceil/2^{63}$, approximately $\binom{n}{2}(2\delta-1)/M_{\min}$.

## 2. What is not constrained

- **Offsets** are arbitrary integers, fixed independently of the draws. They need not be ordered, distinct or non-negative.
- **Bounds** may differ between candidates. Each must lie in $[M_{\min}, 2^{63}]$, and nothing ties them to `maxDelay` or to any `SchedulerSettings`.
- **$n = 1$.** Both sides are $0$: a single candidate is always uncontested and $\binom{1}{2} = 0$. The statement holds but says nothing.
- **$hn$ is necessary.** For $n = 0$ the single (empty) draw vector is contested, because `Uncontested` needs a witness. The left side would be $1/1 = 1$ and the right side $0$.
- **$h\delta$ is not needed for truth.** For $\delta = 0$, every draw is uncontested when $n \ge 1$ (a minimizer is a witness), so the left side is $0$. The right side is also $0$.
- **$hM$ is needed.** For $M_{\min} = 0$ the right side is $0$.
- **The upper half of $hbound$ ($\mathrm{bound}(i) \le 2^{63}$) appears not to be needed for truth.** With a bound above $2^{63}$, each delay value comes from at most $2$ of the $2^{64}$ draws, and $2 \le 2\lceil 2^{63}/M_{\min}\rceil$.
- **Trivial regime.** The right side can be $\ge 1$, which makes the statement trivially true. For example, with $n = 3$ and $\delta = 100$ this happens exactly when $1 \le M_{\min} \le 597$.
- **Scope.** This is a single round. The statement does not say that an uncontested round leads to a successful election, and $\delta$ is a free parameter not tied to any latency or election duration.
- **Satisfiable, not vacuous.** For example $n = 2$, $\delta = M_{\min} = 1$, constant offsets, and $\mathrm{bound} \equiv 1$.

## 3. Plain-language summary

Consider one round of $n \ge 1$ competing election timers with arbitrary fixed offsets, bounds between $M_{\min}$ and $2^{63}$, and independent uniform 64-bit draws. The probability that no candidate fires at least $\delta$ ahead of every other is at most $\binom{n}{2}(2\delta-1)\lceil 2^{63}/M_{\min}\rceil/2^{63}$. That is $\binom{n}{2}$ times the right-hand side of `close_pair_prob`.
