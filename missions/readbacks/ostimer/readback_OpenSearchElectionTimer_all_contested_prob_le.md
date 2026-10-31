# Read-back: `OpenSearchElectionTimer.all_contested_prob_le`

## Notions used

**Draws and delays.** A draw is an element of $\mathrm{Fin}(2^{64})$, read as the Java `long` $\mathrm{toLong}(x) = x - 2^{63}$. $\mathrm{nonNegative}(n)$ is $0$ if $n = -2^{63}$ and $|n|$ otherwise. $\mathrm{randomDelay}(M, x) = (\mathrm{nonNegative}(x - 2^{63}) \bmod M) + 1 \in \mathbb{N}$.

**Fire times.** Given $o : \mathrm{Fin}\,n \to \mathbb{Z}$, $\beta : \mathrm{Fin}\,n \to \mathbb{N}$ and $y : \mathrm{Fin}\,n \to \mathrm{Fin}(2^{64})$, candidate $i$ fires at
$$T_i = o(i) + \mathrm{randomDelay}(\beta(i), y(i)) \in \mathbb{Z}.$$

**Uncontested.** $\mathrm{Uncontested}(o, \beta, \delta, y) \iff \exists i,\ \forall j \ne i,\ T_i + \delta \le T_j$. For $\delta \ge 1$ and $n \ge 1$, its negation ("contested") holds iff $n \ge 2$ and the two smallest fire times, counted with multiplicity, differ by less than $\delta$.

**`contestedBound`.** $q := \mathrm{contestedBound}(n, \delta, M_{\min}) = \binom{n}{2}(2\delta \mathbin{\dot-} 1)\lfloor (2^{63}+M_{\min}-1)/M_{\min}\rfloor/2^{63} \in \mathbb{Q}$. For $\delta, M_{\min} \ge 1$ this is $\binom{n}{2}(2\delta-1)\lceil 2^{63}/M_{\min}\rceil/2^{63}$.

## 1. Declaration

```lean
theorem OpenSearchElectionTimer.all_contested_prob_le (n K δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Int)
    (bound : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Nat)
    (hbound : ∀ k X i, Mmin ≤ bound k X i ∧ bound k X i ≤ 2 ^ 63)
    (hcausal : ∀ k X X', (∀ m : Fin K, m < k → X m = X' m) → offset k X = offset k X' ∧ bound k X = bound k X') :
    ((Finset.univ.filter (fun X : Fin K → Fin n → Fin (2 ^ 64) =>
        ∀ k, ¬ Uncontested (offset k X) (bound k X) δ (X k))).card : ℚ) / (2 ^ 64) ^ (n * K) ≤
      contestedBound n δ Mmin ^ K
```

**Binders and hypotheses, in order:**
- $n, K, \delta, M_{\min} \in \mathbb{N}$;
- $hn : 1 \le n$;
- $h\delta : 1 \le \delta$;
- $hM : 1 \le M_{\min}$.
- $\mathrm{offset}$: for each round $k \in \mathrm{Fin}\,K$ and each full draw matrix $X : \mathrm{Fin}\,K \to \mathrm{Fin}\,n \to \mathrm{Fin}(2^{64})$, an offset vector $\mathrm{offset}(k, X) : \mathrm{Fin}\,n \to \mathbb{Z}$.
- $\mathrm{bound}$: likewise, a bound vector $\mathrm{bound}(k, X) : \mathrm{Fin}\,n \to \mathbb{N}$.
- $hbound$: for all $k$, $X$ and $i$, $M_{\min} \le \mathrm{bound}(k, X)(i) \le 2^{63}$.
- $hcausal$: for all $k$, $X$ and $X'$, if $X(m) = X'(m)$ for every round $m \in \mathrm{Fin}\,K$ with $m < k$ (numeric order on round indices), then $\mathrm{offset}(k, X) = \mathrm{offset}(k, X')$ and $\mathrm{bound}(k, X) = \mathrm{bound}(k, X')$, as functions on $\mathrm{Fin}\,n$. In words: round $k$'s offsets and bounds depend on $X$ only through the draws of strictly earlier rounds.

**Conclusion** (in $\mathbb{Q}$):
$$\frac{\#\big\{X : \forall k \in \mathrm{Fin}\,K,\ \neg\,\mathrm{Uncontested}\big(\mathrm{offset}(k, X),\ \mathrm{bound}(k, X),\ \delta,\ X(k)\big)\big\}}{(2^{64})^{nK}} \;\le\; q^K .$$

**Probability reading.** $X(k)(i)$ is candidate $i$'s draw in round $k$, and all $nK$ draws are independent and uniform on $\mathrm{Fin}(2^{64})$. The offsets and bounds of each round are chosen by a deterministic strategy that sees only the draws of earlier rounds. The probability that all $K$ rounds are contested is at most $q^K$, with $q = \binom{n}{2}(2\delta-1)\lceil 2^{63}/M_{\min}\rceil/2^{63}$. Equivalently, the probability that none of the first $K$ rounds is uncontested is at most $q^K$.

## 2. What is not constrained

- **The strategy is arbitrary, subject only to $hcausal$ and $hbound$.**
  - Offsets may be any integers and may vary with $k$ and with past draws, including other candidates' past draws.
  - Nothing requires rounds to be ordered in time: round $k$'s fire times may precede round $k-1$'s.
  - Nothing requires offsets to relate to earlier fire times or grace periods.
  - Nothing requires bounds to relate to `maxDelay` or to grow with $k$.
- **What the strategy cannot do.** It is deterministic. It cannot depend on the draws of round $k$ itself, so it cannot react within a round to who fired first. It cannot depend on later rounds. There is no randomness other than the draws.
- **The same $n$ candidates take part in every round.** Each draws a fresh value each round. No candidate can sit out a round or join later, and $n$ is fixed.
- **Edge cases:**
  - $K = 0$: both sides equal $1$. The quantifier over rounds is empty, $(2^{64})^0 = 1$, and $q^0 = 1$.
  - $n = 1$ with $K \ge 1$: $q = 0$, and the left side is $0$ (a lone candidate is always uncontested).
- **$hn$ is necessary when $K \ge 1$.** For $n = 0$ every round is contested, so the left side is $1$ while the right side is $0^K = 0$.
- **$h\delta$ is not needed for truth.** For $\delta = 0$ every round is uncontested when $n \ge 1$, and $q = 0$.
- **$hM$ is needed.** For $M_{\min} = 0$, $q = 0$.
- **Trivial regime.** If $q \ge 1$ the statement is trivially true. For example, with $n = 3$ and $\delta = 100$ this happens exactly when $1 \le M_{\min} \le 597$.
- **Scope.** The statement says nothing about what happens in an uncontested round. It does not relate "round $k$" to the scheduler's attempt $k$; the docstring calls grouping timers into rounds an abstraction.
- **Satisfiable, not vacuous.** Constant (draw-independent) offsets and bounds satisfy $hcausal$.

## 3. Plain-language summary

Consider $K$ successive rounds of $n \ge 1$ competing timers, with fresh independent uniform 64-bit draws in each round. An adversary chooses each round's offsets and bounds (bounds between $M_{\min}$ and $2^{63}$), knowing only the draws of earlier rounds. Then the probability that every one of the $K$ rounds is contested is at most $\mathrm{contestedBound}(n, \delta, M_{\min})^K$. The adversary in the statement cannot see the current round's draws, and the set of candidates is the same in every round.
