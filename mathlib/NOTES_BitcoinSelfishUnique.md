# NOTES — BitcoinSelfishUnique

Uniqueness of the stationary distribution of the Eyal–Sirer selfish-mining chain
(I. Eyal, E. G. Sirer, *Majority is not Enough: Bitcoin Mining is Vulnerable*, FC 2014,
arXiv:1311.0243, Section 4). Files: `Definitions/Def_BitcoinSelfishUnique.lean` (the notion of a
stationary distribution; imports `Definitions/Def_BitcoinSelfishMining.lean`, the model) and
`Solutions/Sol_BitcoinSelfishUnique_all.lean` (8 public theorems, no `sorry`, every public theorem
depends only on `[propext, Classical.choice, Quot.sound]`).

## The model (Definitions)

The chain is the one of `Def_BitcoinSelfishMining`: states `State := zero | tie | lead n`
(`lead n` = private lead of `n + 1` blocks, `tie` = the paper's `0'`), one-step transition
probabilities `P α γ s t`, and `stateSum f = f zero + f tie + ∑' n, f (lead n)` for sums over the
countable state space. `stationary α` is the paper's distribution (eq. (7)),
`denom α = 2α³ - 4α² + 1`.

New in this file:

```lean
structure IsStationary (α γ : ℝ) (π : State → ℝ) : Prop where
  nonneg    : ∀ s, 0 ≤ π s
  summable  : Summable (fun n : ℕ => π (.lead n))
  mass      : stateSum π = 1
  invariant : ∀ s, π s = stateSum (fun t => π t * P α γ t s)
```

A stationary distribution is a nonnegative function on the states whose values on the leads are
summable (so `stateSum π` is a genuine infinite sum, not the `tsum` junk value `0`), of total
mass one, and invariant under one step of the chain.

## Theorems (`BitcoinSelfishUnique.<name>`)

1. `stationary_isStationary` (`0 < α < 1/2`, any `γ`): `IsStationary α γ (stationary α)` — the
   paper's distribution is a stationary distribution (nonnegativity, geometric summability, total
   mass one and the balance equations, re-proved privately in this file).
2. Balance identities of *any* stationary distribution, with **no hypothesis on `α` or `γ`**
   (they follow from `invariant` alone, because only finitely many states lead into a given
   state and the three transition probabilities out of the tie add up to `1` identically):
   * `balance_zero_of`: `π 0 = (1-α) π 0 + π 0' + (1-α) π 2`;
   * `balance_tie_of`: `π 0' = (1-α) π 1`;
   * `balance_one_of`: `π 1 = α π 0`;
   * `balance_two_of`: `π 2 = α π 1 + (1-α) π 3`;
   * `balance_lead_of`: `π (n+3) = α π (n+2) + (1-α) π (n+4)`
   (paper numbering; in Lean `π k` is `π (.lead (k-1))`).
3. `geometric_of_isStationary` (`0 < α < 1/2`): `IsStationary α γ π → ∀ n,
   π (lead (n+1)) = (α/(1-α)) · π (lead n)`.
4. `stationary_unique` (`0 < α < 1/2`): `IsStationary α γ π → ∀ s, π s = stationary α s`.

## Proof structure

* **Inflow lemmas.** For an arbitrary `π : State → ℝ` the sum `stateSum (t ↦ π t · P t s)` is
  computed in closed form for each target `s` (`inflow_zero`, `inflow_tie`, `inflow_one`,
  `inflow_two`, `inflow_lead`), by `tsum_eq_single` / `tsum_eq_sum` on the one or two leads that
  can reach `s` and `simp` on `P`, `step`, `outcomeProb`. These are the same computations as in
  `stationary_balance` of `BitcoinSelfishMining`, but for a general `π`; they give both
  directions at once: `stationary_isStationary.invariant` is `inflow_* ▸ balance identity of
  stationary α`, and `balance_*_of` is `inflow_* ▸ h.invariant s`.
* **Geometric recursion.** Let `r = α/(1-α)` and `p k = π (lead k)`. `balance_two_of` and
  `balance_lead_of` give, uniformly for all `k`, `p (k+1) = α p k + (1-α) p (k+2)` (`recur`),
  i.e. `(1-α) p (k+2) = p (k+1) - α p k`. Hence `q k = p (k+1) - r p k` satisfies
  `q (k+1) = q k` (`q_step`, using `(1-α) r = α`), so `q k = q 0 =: c` (`q_const`).
  Then `p (k+1) = c + r p k`, which unrolls to `p k - L = r^k (p 0 - L)` with `L = c/(1-r)`
  (`closed_form`). Since `0 ≤ r < 1`, `p k → L`; since `p` is summable, `p k → 0`
  (`Summable.tendsto_atTop_zero`), so `L = 0` by uniqueness of limits, hence `c = 0`, i.e.
  `p (k+1) = r p k` for all `k`.
* **Uniqueness.** From 3, `p n = r^n p 0`; `balance_one_of` and `balance_tie_of` express `p 0`
  and `π tie` through `π zero`; `mass = 1` with `tsum_geometric_of_lt_one` becomes
  `π zero · (1 + α(1-α) + α(1-α)/(1-2α)) = 1`, i.e. `π zero = (1-2α)/denom α`; the three cases
  of `stationary α` then follow by `field_simp; ring`.

## Remarks and limits

* The balance lemmas (2) need no hypotheses at all; `γ` never matters because the row of `P`
  out of the tie sums to `α + (1-α)γ + (1-α)(1-γ) = 1` for every `γ`.
* The hypothesis `nonneg` of `IsStationary` is not used in the uniqueness proof: any signed,
  lead-summable, invariant `π` of total mass one equals `stationary α`. Summability is essential
  (it is what kills the second solution `c ≠ 0` of the recursion), and so is `0 < α < 1/2`
  (`r < 1`; for `α ≥ 1/2` the chain is not positive recurrent and has no stationary
  distribution of the above kind).
* Not proved (out of scope): ergodic/limit theorems (convergence of the chain or of time averages
  to `stationary α`); only the algebraic uniqueness of the invariant probability vector.
