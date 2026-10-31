# Read-back: `OpenSearchElectionTimer.close_pair_prob`

## Notions used

**Draws.** A draw is an element of $\mathrm{Fin}(2^{64})$, read as the Java `long` $\mathrm{toLong}(x) = x - 2^{63}$.

**`nonNegative`.** $\mathrm{nonNegative}(n) = 0$ if $n = -2^{63}$, and $|n|$ otherwise.

**`randomDelay`.** $\mathrm{randomDelay}(M, x) = (\mathrm{nonNegative}(x - 2^{63}) \bmod M) + 1$, with the natural-number remainder.
- For $M \ge 1$ the value is in $[1, M]$.
- For $M = 0$ the value is $\mathrm{nonNegative}(x - 2^{63}) + 1$, since Lean has $a \bmod 0 = a$.
- For $1 \le d \le M \le 2^{63}$, exactly $2(\lfloor (2^{63}-d)/M\rfloor + 1) \le 2\lceil 2^{63}/M\rceil$ draws give value $d$. This is the content of the sibling theorems `randomDelay_card` and `randomDelay_near_uniform`; it is used here only to explain the bound.

**`contestedBound`.** $\mathrm{contestedBound}(n, \delta, M_{\min}) = \binom{n}{2}(2\delta \mathbin{\dot-} 1)\lfloor (2^{63}+M_{\min}-1)/M_{\min}\rfloor / 2^{63}$ in $\mathbb{Q}$. The present statement does not use the name, but its right-hand side equals $\mathrm{contestedBound}(2, \delta, M_{\min})$, because $\binom{2}{2} = 1$.

## 1. Declaration

```lean
theorem OpenSearchElectionTimer.close_pair_prob (a b : Int) (Ma Mb Mmin δ : Nat) (hM : 1 ≤ Mmin)
    (hMb : Mmin ≤ Mb ∧ Mb ≤ 2 ^ 63) (hδ : 1 ≤ δ) :
    ((Finset.univ.filter (fun p : Fin (2 ^ 64) × Fin (2 ^ 64) =>
        |(a + randomDelay Ma p.1) - (b + randomDelay Mb p.2)| < δ)).card : ℚ) / (2 ^ 64) ^ 2 ≤
      (2 * δ - 1 : ℕ) * ((2 ^ 63 + Mmin - 1) / Mmin : ℕ) / 2 ^ 63
```

**Binders:** $a, b \in \mathbb{Z}$; $M_a, M_b, M_{\min}, \delta \in \mathbb{N}$.

**Hypotheses, in order:**
- $hM : 1 \le M_{\min}$;
- $hMb : M_{\min} \le M_b \wedge M_b \le 2^{63}$;
- $h\delta : 1 \le \delta$.

**Conclusion** (in $\mathbb{Q}$). For a pair of draws $p = (p_1, p_2) \in \mathrm{Fin}(2^{64})^2$, define the integers
$$T_1(p) = a + \mathrm{randomDelay}(M_a, p_1), \qquad T_2(p) = b + \mathrm{randomDelay}(M_b, p_2).$$
The theorem asserts
$$\frac{\#\{p \in \mathrm{Fin}(2^{64})^2 : |T_1(p) - T_2(p)| < \delta\}}{(2^{64})^2} \;\le\; \frac{(2\delta - 1) \cdot \lceil 2^{63}/M_{\min}\rceil}{2^{63}} .$$

**How the Lean terms elaborate:**
- The difference and the absolute value are computed in $\mathbb{Z}$, with $\delta$ cast to $\mathbb{Z}$. So $|T_1 - T_2| < \delta$ means $|T_1 - T_2| \le \delta - 1$.
- `(2 * δ - 1 : ℕ)` is a truncated natural subtraction. By $h\delta$ it equals $2\delta - 1$.
- `((2 ^ 63 + Mmin - 1) / Mmin : ℕ)` is a natural floor division. By $hM$ it equals $\lceil 2^{63}/M_{\min}\rceil$.
- Both natural numbers are cast to $\mathbb{Q}$.

**Probability reading.** $p_1$ and $p_2$ are independent and uniform on $\mathrm{Fin}(2^{64})$. The probability that the two fire times $T_1$ and $T_2$ are less than $\delta$ apart is at most $(2\delta-1)\lceil 2^{63}/M_{\min}\rceil/2^{63}$, which is approximately $(2\delta - 1)/M_{\min}$.

## 2. What is not constrained

- **$a$ and $b$** are arbitrary integers. The bound does not depend on them.
- **$M_a$ is completely unconstrained.** It may be any natural number, including:
  - $0$, where Lean's $\mathrm{randomDelay}(0, x) = \mathrm{nonNegative}(x - 2^{63}) + 1$. This is not a value Java produces, since Java asserts `0 < upperBound`.
  - values above $2^{63}$.

  The hypotheses are asymmetric: only $M_b$ is bounded, from below by $M_{\min}$ and from above by $2^{63}$. The bound therefore rests on the randomness of the second draw $p_2$ alone. For each fixed $p_1$, there are at most $2\delta - 1$ integer values $d$ with $|T_1 - b - d| < \delta$, and each value has at most $2\lceil 2^{63}/M_b\rceil \le 2\lceil 2^{63}/M_{\min}\rceil$ preimages.
- **$M_{\min}$** enters only as a lower bound on $M_b$. The right side does not involve $M_b$ itself.
- **$h\delta$ is not needed for truth.** For $\delta = 0$ the event $|\cdot| < 0$ is empty, and the right side is $0$ (because $2 \cdot 0 \mathbin{\dot-} 1 = 0$). The result is $0 \le 0$.
- **$hM$ is needed.** For $M_{\min} = 0$, Lean's division by zero makes the right side $0$, while the left side can be positive.
- **The upper half of $hMb$ ($M_b \le 2^{63}$) appears not to be needed for truth.** For $M_b > 2^{63}$, each delay value has at most $2$ preimages, and $2 \le 2\lceil 2^{63}/M_{\min}\rceil$.
- **Trivial regime.** When $(2\delta-1)\lceil 2^{63}/M_{\min}\rceil \ge 2^{63}$, roughly $2\delta - 1 \ge M_{\min}$, the right side is at least $1$ and the statement is trivially true.
- **The bound is attained.** Take $M_a = 1$ (so $\mathrm{randomDelay}(1, \cdot) \equiv 1$), $a = b + 100$, $M_b = M_{\min} = 1024$ and $\delta = 2$. Then both sides equal $3/1024$ (I computed this exactly). So the inequality cannot be improved in general.
- **Satisfiable, not vacuous.** For example $M_{\min} = M_b = \delta = 1$.

## 3. Plain-language summary

Two candidates fire at arbitrary integer offsets plus random delays drawn from two independent uniform 64-bit draws. The probability that they fire less than $\delta$ apart is at most $(2\delta-1)\lceil 2^{63}/M_{\min}\rceil/2^{63}$, about $(2\delta-1)/M_{\min}$. This requires the second candidate's bound to lie between $M_{\min}$ and $2^{63}$; the first candidate's bound is unrestricted.
