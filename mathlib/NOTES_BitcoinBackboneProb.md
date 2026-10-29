# NOTES — `BitcoinBackboneProb`: the probabilistic round model behind `Execution.Typical`

Reference: Garay, Kiayias, Leonardos, *The Bitcoin Backbone Protocol*, ePrint 2014/765
(Section 3, Definition 9 "typical execution", Theorem 10). This development derives the
deterministic hypothesis `BitcoinBackbone.Execution.Typical` of `NOTES_BitcoinBackbone.md` with high
probability, using Hoeffding's inequality (Mathlib has it), and composes it with the deterministic
theorems.

Files: `Definitions/Def_BitcoinBackboneProb.lean` (model, unchanged from the earlier draft),
`Solutions/Sol_BitcoinBackboneProb_all.lean` (22 public theorems). No `sorry`. Every public theorem
depends only on `[propext, Classical.choice, Quot.sound]`. Every statement elaborates with only
`import Definitions.Def_BitcoinBackboneProb` and `open BitcoinBackboneProb BitcoinBackbone`
(names from `MeasureTheory`/`ProbabilityTheory` are fully qualified or are global notation).
Pipeline: `stubs` gives 22 stubs and `build errors: 0`; `split` gives `errors=0` for all 22 files.
Split files whose proofs need other public theorems import them as `Theorems.Thm_*` stubs, so
their `#print axioms` shows `sorryAx`. That is how the pipeline handles dependencies. The
monolithic file is axiom-clean.

## Model (Definitions file)

* `ber p = bernoulliMeasure true false p` on `Bool`, with `p : unitInterval`.
* `Round n t = (Fin n → Bool) × (Fin t → Bool)`: which honest queries and which adversarial queries
  succeed. `roundMeasure n t p` is the product of Bernoulli(`p`) measures (`Measure.pi` twice and
  then `.prod`).
* `Trace n t = ℕ → Round n t`, with law `P n t p = Measure.infinitePi (fun _ => roundMeasure n t p)`.
* `honestCount`, `advCount`; `roundX = [honestCount > 0]`, `roundY = [honestCount = 1]`; the trace
  variables are `X ω r`, `Y ω r` and `Z ω r = advCount (ω r)`.
* `margin n t p = n p (1-p)^(n-1) - t p` (= E[Y] − E[Z]); `rate n t p = margin² / (2 (t+1)²)`.
* `TypicalOn ω lam L`: the `Typical` inequality on every window `[a,b]` with `a+lam ≤ b ≤ L`.
* `toExecution ω L base advParent`: the `BitcoinBackbone.Execution` induced on the horizon `[1,L]`.
  Round 0 has no honest mining. After `L`, party 0 mines alone and the adversary finds nothing.
  `TypicalTrunc ω lam L` means this execution is `Typical lam`.

## Public theorems

Rung 1 (independence and law of the rounds)
* `iIndepFun_rounds`: the coordinates `ω ↦ ω r` are `iIndepFun` under `P n t p`.
* `map_eval_P`: `(P n t p).map (· r) = roundMeasure n t p`.

Rung 2 (expectations and honest majority)
* `integral_roundY` / `expect_Y`: `E[Y_r] = n p (1-p)^(n-1)`.
* `integral_roundX` / `expect_X`: `E[X_r] = 1 - (1-p)^n`.
* `integral_advCount` / `expect_Z`: `E[Z_r] = t p`.
* `expect_Y_sub_expect_Z`: `E[Y_r] - E[Z_r] = margin n t p`.
* `margin_ge_of_honest_majority`: `t ≤ (1-δ) n` and `n p ≤ δ/2` imply `margin ≥ δ p n / 2`
  (by Bernoulli's inequality).
* `expect_Z_add_le_expect_Y`: under the same conditions, `E[Z_r] + δ p n / 2 ≤ E[Y_r]`.
* `expect_Z_lt_expect_Y`: adding `δ, p, n > 0` gives `E[Z_r] < E[Y_r]`.

Rung 3 (per-window concentration, exponential, by Hoeffding)
* `sets_hoeffding`: for finite `T ⊆ S` and slack `j`,
  `P(∑_{T} Y + j ≤ ∑_{S} Z) ≤ exp(-2 ε² / (|S| (t+1)²))`, where `ε = j + |T| E[Y] - |S| E[Z] ≥ 0`.
* `window_bound`: for the window `[a, a+k]` with `k ≥ 1` and `2tp ≤ (k-1)·margin`,
  `P(∑_{Ioo} Y ≤ ∑_{Icc} Z) ≤ exp(-2((k-1)·margin - 2tp)² / ((k+1)(t+1)²))`.
* `window_bound_rate`: if `margin > 0` and `4tp ≤ (k-3)·margin`, the same probability is
  `≤ exp(-rate·(k+1))`.

Rung 4 (union bound over the horizon)
* `typicalOn_failure_le_of_window`: if every window of length `≥ lam` fails with probability
  `≤ β` (and `lam ≥ 1`), then `P(¬TypicalOn ω lam L) ≤ L² β`.
* `typicalOn_failure_le`: `P(¬TypicalOn) ≤ L² exp(-rate (lam+1))`, assuming `lam ≥ 1`,
  `margin > 0` and `4tp ≤ (lam-3)·margin`.
* `typicalOn_prob_ge`: the same bound written as `1 - L² exp(-rate(lam+1)) ≤ P(TypicalOn)`.

Rung 5 (end to end)
* `typical_toExecution_iff`: typicality of the induced execution does not depend on
  `base`/`advParent`.
* `typicalTrunc_failure_le`: `P(¬TypicalTrunc ω lam L) ≤ (L+1)² exp(-rate(lam+1))` for `lam ≥ 2`.
  This covers every window, including those crossing or beyond the horizon. A window crossing
  the horizon from start `a` reduces to one Hoeffding event on `Icc a L` against `Ioc a L` with
  slack `a+lam-(L+1)`.
* `backbone_failure_le` / `backbone_prob_ge`: for any property `Q` with
  `hdet : ∀ E, E.Legal → E.Typical lam → Q E`, with probability at least
  `1 - (L+1)² exp(-rate(lam+1))` every legal induced execution satisfies `Q`. The quantifier
  over every `base`/`advParent` (adaptive network/adversary) sits inside the event. Bounds are
  for outer measure, so no measurability of that event is needed.
  Instantiation (checked in a scratch file importing `Solutions.Sol_BitcoinBackbone_all`):
  `Q E := ∀ p₁ p₂ r₁ r₂, p₁ < E.n → p₂ < E.n → r₁ ≤ r₂ → (E.chain p₁ r₁).take (len - 2*lam) <+: E.chain p₂ r₂`,
  `hdet := fun E hE hT .. => BitcoinBackbone.common_prefix E hE lam hT ..`. This gives "common prefix
  with probability ≥ 1 − (L+1)² e^{−rate(λ+1)}". It is not a public theorem here because split
  files cannot import another namespace's solutions without pulling in `sorry` stubs.

**Rung reached: 5** (all rungs, with exponential Hoeffding bounds rather than Chebyshev).

## Mathlib used

`ProbabilityTheory.iIndepFun_infinitePi`, `Measure.infinitePi_map_eval`,
`HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` (Hoeffding), `hasSubgaussianMGF_of_mem_Icc`
(Hoeffding's lemma), `integral_fintype_prod_eq_prod` (Fubini on finite products),
`integral_bernoulliMeasure`, `integral_fun_fst/snd`, `measureReal_biUnion_finset_le`.
Mathlib had no binomial-distribution facts on `Measure.pi` Bernoullis (e.g. `P(count = 1)`). These
were proved by writing the indicators as sums of products of coordinate indicators.

## Limits

* Flat model with `q = 1` (one query per party per round), static difficulty, synchronous rounds.
  The constants are Hoeffding's (range `t+1` per round), not the paper's multiplicative
  Chernoff `(1 ± ε)` bounds, so the rate `margin²/(2(t+1)²)` is weak when `t` is large and `p` is
  small. Multiplicative Chernoff for Bernoulli sums is not in Mathlib.
* The paper's bounds on `X(S)` are not needed by the deterministic layer and are not proved,
  apart from `E[X]`.
* The window-length condition `4tp ≤ (λ-3)·margin` and `λ ≥ 2` are sufficient conditions chosen
  for clean statements. `sets_hoeffding` / `window_bound` give the sharp Hoeffding exponent.
* Union-bound constants: `L²` for in-horizon windows and `(L+1)²` end to end.
