# NOTES — BitcoinSelfishMining

Formalization of the selfish-mining analysis of I. Eyal and E. G. Sirer, *Majority is not Enough:
Bitcoin Mining is Vulnerable*, Financial Cryptography and Data Security 2014 (arXiv:1311.0243),
Section 4. Files: `Definitions/Def_BitcoinSelfishMining.lean` (model) and
`Solutions/Sol_BitcoinSelfishMining_all.lean` (17 public theorems, no `sorry`, every public theorem
depends only on `[propext, Classical.choice, Quot.sound]`).

## The model (Definitions)

* Parameters: `α : ℝ` the pool's hashrate fraction, `γ : ℝ` the fraction of honest hashrate that
  mines on the pool's block during a tie. Hypotheses used by the theorems: `0 < α`, `α < 1/2`,
  and (for the threshold) `γ ≤ 1` (`0 ≤ γ` is accepted as a hypothesis but not needed).
* States `State := zero | tie | lead (n : ℕ)`. `lead n` is a private lead of **n + 1** blocks:
  `lead 0` = the paper's state 1, `lead 1` = state 2, `lead (n+2)` = state `n+3`; `tie` = state `0'`.
  This encoding avoids junk states and proof arguments; the paper's `p_k` (k ≥ 1) is
  `stationary α (lead (k-1))`.
* Step outcomes `Outcome := pool | honestOnPool | honestOnOthers` with probabilities
  `α`, `(1-α)γ`, `(1-α)(1-γ)` (`outcomeProb`). The two honest outcomes differ only in the tie.
* `step : State → Outcome → State` is the transition function of the paper's Figure 1;
  `poolGain`, `othersGain : State → Outcome → ℕ` are the blocks credited at each transition
  (paper eqs. (8)–(9)): tie+pool → pool 2; tie+honestOnPool → pool 1, others 1;
  tie+honestOnOthers → others 2; zero+honest → others 1; lead 2 + honest → pool 2;
  lead ≥ 3 + honest → pool 1; everything else 0.
* `P α γ s t = Σ_o [step s o = t] · outcomeProb α γ o` (one-step transition probability),
  `poolExpGain`, `othersExpGain` (expected credited blocks per step from a state).
* `stateSum f = f zero + f tie + ∑' n, f (lead n)` is the sum over the countable state space
  (tail as a Mathlib `tsum`, which is `0` for a non-summable family; all families we sum are
  proved summable or have finite support).
* `stationary α` is the paper's claimed distribution (eq. (7)) with `denom α = 2α³ - 4α² + 1`.
* `poolRevenue α γ = stateSum (p_s · poolExpGain s)`, `othersRevenue` likewise,
  `relativeRevenue = poolRevenue / (poolRevenue + othersRevenue)` (eq. (10)),
  `closedForm α γ = (α(1-α)²(4α + γ(1-2α)) - α³) / (1 - α(1 + (2-α)α))`,
  `profitThreshold γ = (1-γ)/(3-2γ)` (eq. (11)).

## Theorems (all for `0 < α < 1/2`; `γ` arbitrary unless stated)

1. `denominator_pos`: `0 < 2α³ - 4α² + 1`. `stationary_nonneg`: every `p_s ≥ 0`.
2. `balance_zero`, `balance_tie`, `balance_one`, `balance_two`, `balance_lead`: the explicit
   balance identities `p₀ = (1-α)p₀ + p₀' + (1-α)p₂`, `p₀' = (1-α)p₁`, `p₁ = αp₀`,
   `p₂ = αp₁ + (1-α)p₃`, `p_{n+3} = αp_{n+2} + (1-α)p_{n+4}`.
   `P_row_sum`: `P` is stochastic (each row sums to 1 over `stateSum`).
   `stationary_balance`: for every state `s`, `p_s = stateSum (t ↦ p_t · P t s)` — the paper's
   distribution is invariant for the chain defined by `step`/`outcomeProb` (this derives the
   balance equations from the transition structure rather than postulating them).
3. `tail_sum`: `Σ_{n} p_{lead (n+2)} = p₁ (α/(1-α))² (1-α)/(1-2α)`.
   `total_mass`: `stateSum (stationary α) = 1`.
4. `pool_revenue_eq`, `others_revenue_eq`: the general state-sum definitions of the revenue rates
   reduce exactly to the paper's eqs. (8) and (9) (with the `k ≥ 3` tail as a `tsum`).
   `relative_revenue`: `relativeRevenue α γ = closedForm α γ` (eq. (10)).
5. `threshold` (needs `γ ≤ 1`): `relativeRevenue α γ > α ↔ α > (1-γ)/(3-2γ)` (eq. (11)).
6. `threshold_gamma_zero`: `relativeRevenue α 0 > α ↔ α > 1/3`;
   `threshold_gamma_one`: `relativeRevenue α 1 > α` for every `0 < α < 1/2`.

## What is and is not proved

* Everything in the brief is fully proved; the revenue rates use the genuine infinite tail
  (`tsum`), not its closed form (the closed form is a theorem, `tail_sum`).
* The paper's formula was taken as the definition of `stationary`; stationarity is *verified*
  (`stationary_balance`, `total_mass`), not derived from uniqueness. Not proved: that the chain
  has no other stationary distribution, or any ergodic/limit statement (that the time averages of
  the revenue process converge to the stationary rates). The paper itself argues the latter
  informally, and the statement "R is the pool's long-run revenue share" is interpreted here, as
  in the paper, as the stationary-expected-revenue ratio.
* The case `α ≥ 1/2` and the `α = 0` boundary are excluded by hypothesis (the paper's analysis
  also assumes `0 < α < 1/2`; for `α ≥ 1/2` the chain is not positive recurrent).
* The `γ ≥ 0` hypothesis of `threshold` is stated for faithfulness but unused (only `3 - 2γ > 0`
  is needed, which follows from `γ ≤ 1`).
