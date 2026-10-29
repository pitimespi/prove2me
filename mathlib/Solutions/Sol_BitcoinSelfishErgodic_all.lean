import Definitions.Def_BitcoinSelfishErgodic
import Theorems.Thm_BitcoinSelfishMining_stationary_balance
import Theorems.Thm_BitcoinSelfishMining_total_mass
import Theorems.Thm_BitcoinSelfishMining_stationary_nonneg
import Theorems.Thm_BitcoinSelfishMining_threshold
import Theorems.Thm_BitcoinSelfishUnique_stationary_unique

open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

/-! Helper lemmas: positivity facts about `α` and the ratio `r = α / (1 - α)`. -/

private theorem one_sub_pos {α : ℝ} (h1 : α < 1 / 2) : 0 < 1 - α := by linarith

private theorem ratio_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 < α / (1 - α) :=
  div_pos h0 (one_sub_pos h1)

private theorem ratio_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 ≤ α / (1 - α) :=
  (ratio_pos h0 h1).le

private theorem ratio_lt_one {α : ℝ} (h1 : α < 1 / 2) : α / (1 - α) < 1 :=
  (div_lt_one (one_sub_pos h1)).mpr (by linarith)

/-- `α r^m + (1 - α) r^(m+2) = r^(m+1)` for `r = α / (1 - α)`. -/
private theorem ratio_step {α : ℝ} (h1 : α < 1 / 2) (m : ℕ) :
    α * (α / (1 - α)) ^ m + (1 - α) * (α / (1 - α)) ^ (m + 2) = (α / (1 - α)) ^ (m + 1) := by
  have h1' := (one_sub_pos h1).ne'
  have e : (1 - α) * (α / (1 - α)) = α := mul_div_cancel₀ _ h1'
  linear_combination ((α / (1 - α)) ^ (m + 1) - (α / (1 - α)) ^ m) * e

/-! The one-step inflow `Σ_t μ t · P(t → s)` into each state `s`, for an arbitrary `μ`. Only
finitely many states lead to any given `s`, so these are finite sums (no summability needed).
These are the public theorems `dist_zero`, …, `dist_lead_succ`. -/

/-- One step from `μ`, mass at `zero`: from `zero` (honest block), from the tie (every outcome)
and from lead `2` (honest block). -/
theorem BitcoinSelfishErgodic.dist_zero (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ .zero = (1 - α) * μ .zero + μ .tie + (1 - α) * μ (.lead 1) := by
  unfold BitcoinSelfishErgodic.dist stateSum
  rw [tsum_eq_single 1 ?_]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    rcases b with _ | _ | b
    · simp [P, outcomeSum, step]
    · exact absurd rfl hb
    · simp [P, outcomeSum, step]

/-- One step from `μ`, mass at the tie: from lead `1` on an honest block. -/
theorem BitcoinSelfishErgodic.dist_tie (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ .tie = (1 - α) * μ (.lead 0) := by
  unfold BitcoinSelfishErgodic.dist stateSum
  rw [tsum_eq_single 0 ?_]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    rcases b with _ | _ | b
    · exact absurd rfl hb
    · simp [P, outcomeSum, step]
    · simp [P, outcomeSum, step]

/-- One step from `μ`, mass at lead `1`: from `zero` on a pool block. -/
theorem BitcoinSelfishErgodic.dist_lead_zero (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ (.lead 0) = α * μ .zero := by
  unfold BitcoinSelfishErgodic.dist stateSum
  rw [tsum_eq_single 0 ?_]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    rcases b with _ | _ | b
    · exact absurd rfl hb
    · simp [P, outcomeSum, step]
    · simp [P, outcomeSum, step]

/-- One step from `μ`, mass at lead `2`: from lead `1` (pool block) and lead `3` (honest block). -/
theorem BitcoinSelfishErgodic.dist_lead_one (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ) :
    BitcoinSelfishErgodic.dist α γ μ (.lead 1) = α * μ (.lead 0) + (1 - α) * μ (.lead 2) := by
  unfold BitcoinSelfishErgodic.dist stateSum
  rw [tsum_eq_sum (s := {0, 2}) ?_, Finset.sum_pair (by norm_num)]
  · simp only [P, outcomeSum, step, outcomeProb]
    simp
    ring
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    rcases b with _ | _ | b
    · exact absurd rfl hb.1
    · simp [P, outcomeSum, step]
    · have : b ≠ 0 := by omega
      simp [P, outcomeSum, step, this]

/-- One step from `μ`, mass at lead `n + 3 ≥ 3`: from lead `n + 2` (pool block) and lead `n + 4`
(honest block). -/
theorem BitcoinSelfishErgodic.dist_lead_succ (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (n : ℕ) :
    BitcoinSelfishErgodic.dist α γ μ (.lead (n + 2)) =
      α * μ (.lead (n + 1)) + (1 - α) * μ (.lead (n + 3)) := by
  unfold BitcoinSelfishErgodic.dist stateSum
  rcases n with _ | k
  · rw [tsum_eq_sum (s := {1, 3}) ?_, Finset.sum_pair (by norm_num)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      ring
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · exact absurd rfl hb.1
      · have h1' : b ≠ 1 := by omega
        simp [P, outcomeSum, step, h1']
  · rw [tsum_eq_sum (s := {k + 2, k + 4}) ?_, Finset.sum_pair (by omega)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      ring
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
      · have h1' : b ≠ k := by omega
        have h0' : b ≠ k + 2 := by omega
        simp [P, outcomeSum, step, h1', h0']

/-- Uniform form of the inflow at the leads `n + 1 ≥ 1`. -/
private theorem dist_lead_add_one (α γ : ℝ) (μ : State → ℝ) (n : ℕ) :
    dist α γ μ (.lead (n + 1)) = α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) := by
  rcases n with _ | n
  · exact dist_lead_one α γ μ
  · exact dist_lead_succ α γ μ n

/-! Preservation of summability, mass and nonnegativity. -/

private theorem dist_summable {α γ : ℝ} {μ : State → ℝ}
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    Summable (fun n : ℕ => dist α γ μ (.lead n)) := by
  rw [← summable_nat_add_iff 1]
  have : (fun n : ℕ => dist α γ μ (.lead (n + 1))) =
      fun n => α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) := by
    funext n; exact dist_lead_add_one α γ μ n
  rw [this]
  exact (hμ.mul_left α).add (((summable_nat_add_iff 2).2 hμ).mul_left (1 - α))

private theorem dist_lead_tsum {α γ : ℝ} {μ : State → ℝ}
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    ∑' n : ℕ, dist α γ μ (.lead n) =
      α * μ .zero + α * ∑' n : ℕ, μ (.lead n)
        + (1 - α) * (∑' n : ℕ, μ (.lead n) - μ (.lead 0) - μ (.lead 1)) := by
  rw [(dist_summable (α := α) (γ := γ) hμ).tsum_eq_zero_add, dist_lead_zero]
  have e : ∀ n : ℕ, dist α γ μ (.lead (n + 1)) = α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) :=
    dist_lead_add_one α γ μ
  simp_rw [e]
  rw [(hμ.mul_left α).tsum_add (((summable_nat_add_iff 2).2 hμ).mul_left (1 - α)),
    tsum_mul_left, tsum_mul_left]
  have h2 := hμ.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h2
  rw [show ∑' n : ℕ, μ (.lead (n + 2)) = ∑' n : ℕ, μ (.lead n) - μ (.lead 0) - μ (.lead 1) by
    linarith]
  ring

/-- One step of the chain preserves the total mass of a lead-summable `μ`. -/
theorem BitcoinSelfishErgodic.dist_mass (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    BitcoinSelfishMining.stateSum (BitcoinSelfishErgodic.dist α γ μ) =
      BitcoinSelfishMining.stateSum μ := by
  unfold stateSum
  rw [dist_lead_tsum hμ, dist_zero, dist_tie]
  ring

/-- One step of the chain preserves the summability over the leads. -/
theorem BitcoinSelfishErgodic.dist_summable_lead (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    Summable (fun n : ℕ => BitcoinSelfishErgodic.dist α γ μ (.lead n)) := by
  exact dist_summable hμ

/-- One step of the chain preserves nonnegativity (for `0 ≤ α ≤ 1`). -/
theorem BitcoinSelfishErgodic.dist_nonneg (α γ : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : ∀ s, 0 ≤ μ s) (s : BitcoinSelfishMining.State) :
    0 ≤ BitcoinSelfishErgodic.dist α γ μ s := by
  have h1' : 0 ≤ 1 - α := by linarith
  rcases s with _ | _ | _ | _ | n
  · rw [dist_zero]; have := hμ .zero; have := hμ .tie; have := hμ (.lead 1); positivity
  · rw [dist_tie]; have := hμ (.lead 0); positivity
  · rw [dist_lead_zero]; have := hμ .zero; positivity
  · rw [dist_lead_one]; have := hμ (.lead 0); have := hμ (.lead 2); positivity
  · rw [dist_lead_succ]; have := hμ (.lead (n + 1)); have := hμ (.lead (n + 3)); positivity

/-- One step of the chain maps probability distributions to probability distributions. -/
theorem BitcoinSelfishErgodic.isDist_dist (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ) :
    BitcoinSelfishErgodic.IsDist (BitcoinSelfishErgodic.dist α γ μ) :=
  ⟨dist_nonneg α γ h0.le (by linarith) μ hμ.nonneg, dist_summable hμ.summable,
    by rw [dist_mass α γ μ hμ.summable, hμ.mass]⟩

/-- The `n`-step distributions of a probability distribution are probability distributions. -/
theorem BitcoinSelfishErgodic.isDist_distN (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ) (n : ℕ) :
    BitcoinSelfishErgodic.IsDist (BitcoinSelfishErgodic.distN α γ μ n) := by
  induction n with
  | zero => exact hμ
  | succ n ih => exact isDist_dist α γ h0 h1 _ ih

/-- The paper's distribution is a fixed point of one step of the chain
(from `stationary_balance`). -/
theorem BitcoinSelfishErgodic.dist_stationary (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishErgodic.dist α γ (BitcoinSelfishMining.stationary α) =
      BitcoinSelfishMining.stationary α := by
  funext s
  exact (stationary_balance α γ h0 h1 s).symm

/-- The paper's distribution is a fixed point of the `n`-step evolution. -/
theorem BitcoinSelfishErgodic.distN_stationary (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishMining.stationary α) n =
      BitcoinSelfishMining.stationary α := by
  induction n with
  | zero => rfl
  | succ n ih => show dist α γ _ = _; rw [ih, dist_stationary α γ h0 h1]

/-! Point masses. -/

private theorem delta_lead_summable (t : State) :
    Summable (fun n : ℕ => delta t (.lead n)) := by
  rcases t with _ | _ | j
  · simp [delta]
  · simp [delta]
  · have : (fun n : ℕ => delta (.lead j) (.lead n)) = fun n => if n = j then (1:ℝ) else 0 := by
      funext n; simp [delta]
    rw [this]
    exact (hasSum_ite_eq j (1:ℝ)).summable

/-- A point mass is a probability distribution. -/
theorem BitcoinSelfishErgodic.isDist_delta (t : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.IsDist (BitcoinSelfishErgodic.delta t) := by
  refine ⟨fun s => by unfold delta; split_ifs <;> norm_num, delta_lead_summable t, ?_⟩
  unfold stateSum
  rcases t with _ | _ | j
  · simp [delta]
  · simp [delta]
  · have : (fun n : ℕ => delta (.lead j) (.lead n)) = fun n => if n = j then (1:ℝ) else 0 := by
      funext n; simp [delta]
    rw [this, tsum_ite_eq]
    simp [delta]

/-- Every coordinate of a probability distribution is at most one. -/
theorem BitcoinSelfishErgodic.le_one_of_isDist (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : BitcoinSelfishErgodic.IsDist μ) (s : BitcoinSelfishMining.State) : μ s ≤ 1 := by
  have hm := hμ.mass
  unfold stateSum at hm
  have h0 := hμ.nonneg .zero
  have ht := hμ.nonneg .tie
  have hT : 0 ≤ ∑' n : ℕ, μ (.lead n) := tsum_nonneg (fun n => hμ.nonneg _)
  rcases s with _ | _ | n
  · linarith
  · linarith
  · have := hμ.summable.le_tsum n (fun j _ => hμ.nonneg _)
    linarith

/-! Geometric domination of the lead probabilities, uniformly in time: if
`μ (lead m) ≤ C r^m` for all `m` (with `C ≥ 1`), the same holds after one step. -/

private theorem dist_lead_le {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {C : ℝ} (hC : 1 ≤ C) (hb : ∀ m, μ (.lead m) ≤ C * (α / (1 - α)) ^ m) (m : ℕ) :
    dist α γ μ (.lead m) ≤ C * (α / (1 - α)) ^ m := by
  rcases m with _ | m
  · rw [dist_lead_zero, pow_zero, mul_one]
    have := le_one_of_isDist μ hμ .zero
    have := hμ.nonneg .zero
    nlinarith
  · rw [dist_lead_add_one, ← ratio_step h1 m]
    have ha := hb m
    have hb2 := hb (m + 2)
    have h1' : 0 ≤ 1 - α := by linarith
    nlinarith [mul_le_mul_of_nonneg_left ha h0.le, mul_le_mul_of_nonneg_left hb2 h1']

private theorem distN_lead_le_aux {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {C : ℝ} (hC : 1 ≤ C) (hb : ∀ m, μ (.lead m) ≤ C * (α / (1 - α)) ^ m)
    (n m : ℕ) : distN α γ μ n (.lead m) ≤ C * (α / (1 - α)) ^ m := by
  induction n generalizing m with
  | zero => exact hb m
  | succ n ih => exact dist_lead_le h0 h1 (isDist_distN α γ h0 h1 μ hμ n) hC ih m

/-- Geometric domination of the lead probabilities of the chain started at `zero`, uniformly
in time: `P(X_n = lead m) ≤ (α / (1 - α))^m` for every `n`. -/
theorem BitcoinSelfishErgodic.distN_zero_lead_le (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (n m : ℕ) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta .zero) n (.lead m) ≤
      (α / (1 - α)) ^ m := by
  have := distN_lead_le_aux (γ := γ) h0 h1 (isDist_delta .zero) (C := 1) le_rfl
    (fun m => by simpa [delta] using pow_nonneg (ratio_nonneg h0 h1) m) n m
  simpa using this

/-- Geometric domination of the lead probabilities of the chain started at any state `t`,
uniformly in time. -/
theorem BitcoinSelfishErgodic.distN_delta_lead_le (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (t : BitcoinSelfishMining.State) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ,
      BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta t) n (.lead m) ≤
        C * (α / (1 - α)) ^ m := by
  have hr := ratio_pos h0 h1
  rcases t with _ | _ | j
  · exact ⟨1, le_rfl, fun n m => distN_lead_le_aux h0 h1 (isDist_delta .zero) le_rfl
      (fun m => by simpa [delta] using pow_nonneg (ratio_nonneg h0 h1) m) n m⟩
  · exact ⟨1, le_rfl, fun n m => distN_lead_le_aux h0 h1 (isDist_delta .tie) le_rfl
      (fun m => by simpa [delta] using pow_nonneg (ratio_nonneg h0 h1) m) n m⟩
  · have hC : 1 ≤ ((α / (1 - α))⁻¹) ^ j :=
      one_le_pow₀ ((one_le_inv₀ hr).mpr (ratio_lt_one h1).le)
    refine ⟨((α / (1 - α))⁻¹) ^ j, hC, fun n m => distN_lead_le_aux h0 h1 (isDist_delta _) hC
      (fun m => ?_) n m⟩
    simp only [delta]
    split_ifs with h
    · simp only [State.lead.injEq] at h
      subst h
      rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    · positivity

/-! Linearity of one step of the chain (finite sums and scalars), via the inflow formulas. -/

private theorem dist_finsetSum (α γ : ℝ) (f : ℕ → State → ℝ) (F : Finset ℕ) (s : State) :
    dist α γ (fun t => ∑ k ∈ F, f k t) s = ∑ k ∈ F, dist α γ (f k) s := by
  rcases s with _ | _ | _ | _ | n <;>
    simp only [zero_add, BitcoinSelfishErgodic.dist_zero, dist_tie, dist_lead_zero, dist_lead_one,
      dist_lead_succ, Finset.mul_sum, Finset.sum_add_distrib]

private theorem dist_const_mul (α γ : ℝ) (c : ℝ) (μ : State → ℝ) (s : State) :
    dist α γ (fun t => c * μ t) s = c * dist α γ μ s := by
  rcases s with _ | _ | _ | _ | n <;>
    simp only [zero_add, BitcoinSelfishErgodic.dist_zero, dist_tie, dist_lead_zero, dist_lead_one,
      dist_lead_succ] <;> ring

/-- Continuity of one step of the chain in each coordinate (it is a finite linear combination of
at most three coordinates). -/
private theorem tendsto_dist {α γ : ℝ} {y : ℕ → State → ℝ} {ν : State → ℝ}
    (h : ∀ s, Tendsto (fun j => y j s) atTop (𝓝 (ν s))) (s : State) :
    Tendsto (fun j => dist α γ (y j) s) atTop (𝓝 (dist α γ ν s)) := by
  rcases s with _ | _ | _ | _ | n
  · simp only [BitcoinSelfishErgodic.dist_zero]
    exact (((h .zero).const_mul _).add (h .tie)).add ((h (.lead 1)).const_mul _)
  · simp only [dist_tie]; exact (h (.lead 0)).const_mul _
  · simp only [dist_lead_zero]; exact (h .zero).const_mul _
  · simp only [zero_add, dist_lead_one]
    exact ((h (.lead 0)).const_mul _).add ((h (.lead 2)).const_mul _)
  · simp only [dist_lead_succ]
    exact ((h (.lead (n + 1))).const_mul _).add ((h (.lead (n + 3))).const_mul _)

/-! Linearity of `stateSum`. -/

private theorem stateSum_add {f g : State → ℝ} (hf : Summable (fun n : ℕ => f (.lead n)))
    (hg : Summable (fun n : ℕ => g (.lead n))) :
    stateSum (fun s => f s + g s) = stateSum f + stateSum g := by
  unfold stateSum; rw [hf.tsum_add hg]; ring

private theorem stateSum_const_mul (c : ℝ) (f : State → ℝ) :
    stateSum (fun s => c * f s) = c * stateSum f := by
  unfold stateSum; rw [tsum_mul_left]; ring

private theorem stateSum_mul_const (c : ℝ) (f : State → ℝ) :
    stateSum (fun s => f s * c) = stateSum f * c := by
  unfold stateSum; rw [tsum_mul_right]; ring

private theorem stateSum_finsetSum {f : ℕ → State → ℝ} {F : Finset ℕ}
    (hf : ∀ k ∈ F, Summable (fun n : ℕ => f k (.lead n))) :
    stateSum (fun s => ∑ k ∈ F, f k s) = ∑ k ∈ F, stateSum (f k) := by
  unfold stateSum; rw [Summable.tsum_finsetSum hf, Finset.sum_add_distrib, Finset.sum_add_distrib]

/-! Elementary properties of the Cesàro averages. -/

private theorem cesaro_nonneg {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) (n : ℕ) (s : State) : 0 ≤ cesaro α γ μ n s := by
  unfold cesaro
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun k _ => (isDist_distN α γ h0 h1 μ hμ k).nonneg s))

private theorem cesaro_le {α γ : ℝ} {μ : State → ℝ} {s : State} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k, distN α γ μ k s ≤ B) (n : ℕ) : cesaro α γ μ n s ≤ B := by
  unfold cesaro
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hB]
  · have hsum : ∑ k ∈ Finset.range n, distN α γ μ k s ≤ (n : ℝ) * B := by
      have := Finset.sum_le_card_nsmul (Finset.range n) (fun k => distN α γ μ k s) B
        (fun k _ => hb k)
      simpa [Finset.card_range, nsmul_eq_mul] using this
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ μ k s
        ≤ (1 / (n : ℝ)) * ((n : ℝ) * B) := by gcongr
      _ = B := by field_simp

private theorem cesaro_summable {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) (n : ℕ) : Summable (fun m : ℕ => cesaro α γ μ n (.lead m)) := by
  unfold cesaro
  exact (summable_sum (fun k _ => (isDist_distN α γ h0 h1 μ hμ k).summable)).mul_left _

private theorem cesaro_mass {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {n : ℕ} (hn : 1 ≤ n) : stateSum (cesaro α γ μ n) = 1 := by
  have e : cesaro α γ μ n = fun s => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ μ k s := rfl
  rw [e, stateSum_const_mul,
    stateSum_finsetSum (fun k _ => (isDist_distN α γ h0 h1 μ hμ k).summable)]
  rw [Finset.sum_congr rfl (fun k _ => (isDist_distN α γ h0 h1 μ hμ k).mass), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- Almost invariance: `dist (cesaro n) - cesaro n = (distN n - μ) / n`. -/
private theorem cesaro_dist_sub (α γ : ℝ) (μ : State → ℝ) (n : ℕ) (s : State) :
    dist α γ (cesaro α γ μ n) s - cesaro α γ μ n s =
      (1 / (n : ℝ)) * (distN α γ μ n s - μ s) := by
  have e : cesaro α γ μ n = fun s => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ μ k s := rfl
  rw [e, dist_const_mul, dist_finsetSum]
  have e2 : ∀ k, dist α γ (distN α γ μ k) s = distN α γ μ (k + 1) s := fun k => rfl
  simp only [e2]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => distN α γ μ k s)]
  rfl

private theorem cesaro_dist_sub_tendsto {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) (s : State) :
    Tendsto (fun n => dist α γ (cesaro α γ μ n) s - cesaro α γ μ n s) atTop (𝓝 0) := by
  simp only [cesaro_dist_sub]
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat 2
  refine squeeze_zero_norm (fun n => ?_) h2
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / n),
    div_eq_mul_one_div 2 (n : ℝ), mul_comm (2 : ℝ)]
  gcongr
  have := (isDist_distN α γ h0 h1 μ hμ n).nonneg s
  have := le_one_of_isDist _ (isDist_distN α γ h0 h1 μ hμ n) s
  have := hμ.nonneg s
  have := le_one_of_isDist μ hμ s
  rw [abs_le]; constructor <;> linarith

/-! The compactness argument: along any subsequence, the Cesàro averages have a further
subsequence converging pointwise to a stationary distribution, which is `stationary α` by
uniqueness. -/

private theorem cesaro_subseq {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {C : ℝ} (hC : 1 ≤ C)
    (hb : ∀ n m, distN α γ μ n (.lead m) ≤ C * (α / (1 - α)) ^ m)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, Tendsto (fun j => cesaro α γ μ (ns (ms j))) atTop (𝓝 (stationary α)) := by
  have hr0 := ratio_nonneg h0 h1
  have hr1 := ratio_lt_one h1
  have hgeo : Summable (fun m : ℕ => C * (α / (1 - α)) ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  set S : Set (State → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1) with hS
  have hSc : IsCompact S := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hmem : ∀ j, cesaro α γ μ (ns j) ∈ S := by
    intro j
    rw [hS, Set.mem_univ_pi]
    intro s
    exact ⟨cesaro_nonneg h0 h1 hμ _ s,
      cesaro_le zero_le_one (fun k => le_one_of_isDist _ (isDist_distN α γ h0 h1 μ hμ k) s) _⟩
  obtain ⟨ν, hνS, φ, hφ, hlim⟩ := hSc.tendsto_subseq hmem
  refine ⟨φ, ?_⟩
  have hpt : ∀ s, Tendsto (fun j => cesaro α γ μ (ns (φ j)) s) atTop (𝓝 (ν s)) :=
    fun s => tendsto_pi_nhds.1 hlim s
  have hnsφ : Tendsto (fun j => ns (φ j)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hν0 : ∀ s, 0 ≤ ν s := fun s => (Set.mem_univ_pi.1 hνS s).1
  have hνb : ∀ m, ν (.lead m) ≤ C * (α / (1 - α)) ^ m := fun m =>
    le_of_tendsto' (hpt (.lead m)) (fun j => cesaro_le (by positivity) (fun k => hb k m) _)
  have hνsum : Summable (fun m : ℕ => ν (.lead m)) :=
    Summable.of_nonneg_of_le (fun m => hν0 _) hνb hgeo
  have hstat : IsStationary α γ ν := by
    refine ⟨hν0, hνsum, ?_, ?_⟩
    · -- total mass one, by dominated convergence
      have hA : Tendsto (fun j => stateSum (cesaro α γ μ (ns (φ j)))) atTop (𝓝 (stateSum ν)) := by
        unfold stateSum
        refine ((hpt .zero).add (hpt .tie)).add ?_
        refine tendsto_tsum_of_dominated_convergence hgeo (fun m => hpt (.lead m))
          (Eventually.of_forall fun j m => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (cesaro_nonneg h0 h1 hμ _ _)]
        exact cesaro_le (by positivity) (fun k => hb k m) _
      have hB : Tendsto (fun j => stateSum (cesaro α γ μ (ns (φ j)))) atTop (𝓝 1) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hnsφ.eventually_ge_atTop 1] with j hj
        exact (cesaro_mass h0 h1 hμ hj).symm
      exact tendsto_nhds_unique hA hB
    · -- invariance
      intro s
      have hd : Tendsto (fun j => dist α γ (cesaro α γ μ (ns (φ j))) s) atTop (𝓝 (dist α γ ν s)) :=
        tendsto_dist hpt s
      have he : Tendsto (fun j => dist α γ (cesaro α γ μ (ns (φ j))) s - cesaro α γ μ (ns (φ j)) s)
          atTop (𝓝 0) :=
        (cesaro_dist_sub_tendsto h0 h1 hμ s).comp hnsφ
      have := tendsto_nhds_unique (hd.sub (hpt s)) he
      show ν s = dist α γ ν s
      linarith
  have hνeq : ν = stationary α := funext (stationary_unique α γ ν h0 h1 hstat)
  rw [← hνeq]
  exact hlim

/-! Public convergence theorems. -/

/-- **Cesàro convergence from any state.** For the chain started at any state `t`, the expected
fraction of time spent in each state `s` converges to the stationary probability
`stationary α s`. -/
theorem BitcoinSelfishErgodic.cesaro_delta_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (t s : BitcoinSelfishMining.State) :
    Filter.Tendsto (fun n => BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta t) n s)
      Filter.atTop (nhds (BitcoinSelfishMining.stationary α s)) := by
  obtain ⟨C, hC, hb⟩ := distN_delta_lead_le α γ h0 h1 t
  have hpi : Tendsto (fun n => cesaro α γ (delta t) n) atTop (𝓝 (stationary α)) :=
    tendsto_of_subseq_tendsto (fun ns hns => cesaro_subseq h0 h1 (isDist_delta t) hC hb ns hns)
  exact tendsto_pi_nhds.1 hpi s

/-- **Cesàro convergence from `zero`.** For the chain started at `zero`,
`(1/n) Σ_{k<n} P(X_k = s) → stationary α s` for every state `s`. -/
theorem BitcoinSelfishErgodic.cesaro_zero_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) :
    Filter.Tendsto
      (fun n => BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta .zero) n s)
      Filter.atTop (nhds (BitcoinSelfishMining.stationary α s)) :=
  cesaro_delta_tendsto α γ h0 h1 .zero s

/-! Mixing: the chain started at a probability distribution `μ` is the `μ`-mixture of the chains
started at the point masses `delta t`. -/

private theorem mix_summable {μ : State → ℝ} (hμ : IsDist μ) {f : State → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) :
    Summable (fun n : ℕ => μ (.lead n) * f (.lead n)) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (hμ.nonneg _) (hf0 _))
    (fun n => mul_le_of_le_one_right (hμ.nonneg _) (hf1 _)) hμ.summable

private theorem stateSum_delta (μ : State → ℝ) (s : State) :
    stateSum (fun t => μ t * delta t s) = μ s := by
  unfold stateSum delta
  rcases s with _ | _ | m
  · simp
  · simp
  · simp [eq_comm]

private theorem stateSum_mix3 {μ : State → ℝ} (hμ : IsDist μ) {f : State → State → ℝ}
    (hf0 : ∀ t s, 0 ≤ f t s) (hf1 : ∀ t s, f t s ≤ 1) (a b c : ℝ) (s1 s2 s3 : State) :
    stateSum (fun t => μ t * (a * f t s1 + b * f t s2 + c * f t s3)) =
      a * stateSum (fun t => μ t * f t s1) + b * stateSum (fun t => μ t * f t s2)
        + c * stateSum (fun t => μ t * f t s3) := by
  have hs : ∀ s', Summable (fun n : ℕ => μ (.lead n) * f (.lead n) s') :=
    fun s' => mix_summable hμ (fun t => hf0 t s') (fun t => hf1 t s')
  have e : ∀ t, μ t * (a * f t s1 + b * f t s2 + c * f t s3) =
      a * (μ t * f t s1) + b * (μ t * f t s2) + c * (μ t * f t s3) := fun t => by ring
  simp only [e]
  unfold stateSum
  rw [(((hs s1).mul_left a).add ((hs s2).mul_left b)).tsum_add ((hs s3).mul_left c),
    ((hs s1).mul_left a).tsum_add ((hs s2).mul_left b), tsum_mul_left, tsum_mul_left,
    tsum_mul_left]
  ring

private theorem stateSum_mix2 {μ : State → ℝ} (hμ : IsDist μ) {f : State → State → ℝ}
    (hf0 : ∀ t s, 0 ≤ f t s) (hf1 : ∀ t s, f t s ≤ 1) (a b : ℝ) (s1 s2 : State) :
    stateSum (fun t => μ t * (a * f t s1 + b * f t s2)) =
      a * stateSum (fun t => μ t * f t s1) + b * stateSum (fun t => μ t * f t s2) := by
  have hs : ∀ s', Summable (fun n : ℕ => μ (.lead n) * f (.lead n) s') :=
    fun s' => mix_summable hμ (fun t => hf0 t s') (fun t => hf1 t s')
  have e : ∀ t, μ t * (a * f t s1 + b * f t s2) =
      a * (μ t * f t s1) + b * (μ t * f t s2) := fun t => by ring
  simp only [e]
  unfold stateSum
  rw [((hs s1).mul_left a).tsum_add ((hs s2).mul_left b), tsum_mul_left, tsum_mul_left]
  ring

private theorem stateSum_mix1 {μ : State → ℝ} {f : State → State → ℝ} (a : ℝ) (s1 : State) :
    stateSum (fun t => μ t * (a * f t s1)) = a * stateSum (fun t => μ t * f t s1) := by
  have e : ∀ t, μ t * (a * f t s1) = a * (μ t * f t s1) := fun t => by ring
  simp only [e]
  exact stateSum_const_mul a _

/-- One step commutes with mixing. -/
private theorem dist_mix {α γ : ℝ} {μ : State → ℝ} (hμ : IsDist μ) {f : State → State → ℝ}
    (hf0 : ∀ t s, 0 ≤ f t s) (hf1 : ∀ t s, f t s ≤ 1) (s : State) :
    dist α γ (fun s' => stateSum (fun t => μ t * f t s')) s =
      stateSum (fun t => μ t * dist α γ (f t) s) := by
  rcases s with _ | _ | _ | _ | n
  · simp only [BitcoinSelfishErgodic.dist_zero]
    rw [show (fun t => μ t * ((1 - α) * f t .zero + f t .tie + (1 - α) * f t (.lead 1))) =
        fun t => μ t * ((1 - α) * f t .zero + 1 * f t .tie + (1 - α) * f t (.lead 1)) by
      funext t; ring, stateSum_mix3 hμ hf0 hf1]
    ring
  · simp only [dist_tie]
    exact (stateSum_mix1 _ _).symm
  · simp only [dist_lead_zero]
    exact (stateSum_mix1 _ _).symm
  · simp only [zero_add, dist_lead_one]
    exact (stateSum_mix2 hμ hf0 hf1 _ _ _ _).symm
  · simp only [dist_lead_succ]
    exact (stateSum_mix2 hμ hf0 hf1 _ _ _ _).symm

/-- The `n`-step distribution from `μ` is the `μ`-mixture of the `n`-step distributions from
the point masses. -/
theorem BitcoinSelfishErgodic.distN_mix (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ) (n : ℕ)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.distN α γ μ n s =
      BitcoinSelfishMining.stateSum
        (fun t => μ t * BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta t) n s) := by
  induction n generalizing s with
  | zero => exact (stateSum_delta μ s).symm
  | succ n ih =>
    have e : distN α γ μ n = fun s => stateSum (fun t => μ t * distN α γ (delta t) n s) :=
      funext ih
    show dist α γ (distN α γ μ n) s = _
    rw [e]
    exact dist_mix hμ (fun t s => (isDist_distN α γ h0 h1 _ (isDist_delta t) n).nonneg s)
      (fun t s => le_one_of_isDist _ (isDist_distN α γ h0 h1 _ (isDist_delta t) n) s) s

private theorem cesaro_mix {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) (n : ℕ) (s : State) :
    cesaro α γ μ n s = stateSum (fun t => μ t * cesaro α γ (delta t) n s) := by
  unfold cesaro
  simp only [distN_mix α γ h0 h1 μ hμ]
  have e : (fun t => μ t * ((1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ (delta t) k s)) =
      fun t => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, (μ t * distN α γ (delta t) k s) := by
    funext t; rw [← Finset.mul_sum]; ring
  rw [e, stateSum_const_mul, stateSum_finsetSum (fun k _ => mix_summable hμ
    (fun t => (isDist_distN α γ h0 h1 _ (isDist_delta t) k).nonneg s)
    (fun t => le_one_of_isDist _ (isDist_distN α γ h0 h1 _ (isDist_delta t) k) s))]

/-- **Cesàro convergence from any initial distribution.** For the chain started with any
probability distribution `μ`, the expected fraction of time spent in each state `s` converges to
`stationary α s`. -/
theorem BitcoinSelfishErgodic.cesaro_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ)
    (s : BitcoinSelfishMining.State) :
    Filter.Tendsto (fun n => BitcoinSelfishErgodic.cesaro α γ μ n s) Filter.atTop
      (nhds (BitcoinSelfishMining.stationary α s)) := by
  simp only [cesaro_mix h0 h1 hμ]
  have hlim : Tendsto (fun n => stateSum (fun t => μ t * cesaro α γ (delta t) n s)) atTop
      (𝓝 (stateSum (fun t => μ t * stationary α s))) := by
    unfold stateSum
    refine (((cesaro_delta_tendsto α γ h0 h1 .zero s).const_mul _).add
      ((cesaro_delta_tendsto α γ h0 h1 .tie s).const_mul _)).add ?_
    refine tendsto_tsum_of_dominated_convergence hμ.summable
      (fun m => (cesaro_delta_tendsto α γ h0 h1 (.lead m) s).const_mul _)
      (Eventually.of_forall fun n m => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hμ.nonneg _) (cesaro_nonneg h0 h1 (isDist_delta _) n s))]
    exact mul_le_of_le_one_right (hμ.nonneg _) (cesaro_le zero_le_one
      (fun k => le_one_of_isDist _ (isDist_distN α γ h0 h1 _ (isDist_delta _) k) s) n)
  rw [stateSum_mul_const, hμ.mass, one_mul] at hlim
  exact hlim

/-! Revenues as long-run averages. -/

private theorem poolExpGain_zero (α γ : ℝ) : poolExpGain α γ .zero = 0 := by
  simp [poolExpGain, outcomeSum, poolGain]

private theorem poolExpGain_tie (α γ : ℝ) :
    poolExpGain α γ .tie = α * 2 + γ * (1 - α) * 1 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

private theorem poolExpGain_lead_bound {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (m : ℕ) :
    0 ≤ poolExpGain α γ (.lead m) ∧ poolExpGain α γ (.lead m) ≤ 2 := by
  rcases m with _ | _ | m
  · simp [poolExpGain, outcomeSum, poolGain]
  · have e : poolExpGain α γ (.lead 1) = (1 - α) * 2 := by
      simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring
    rw [e]; constructor <;> nlinarith
  · have e : poolExpGain α γ (.lead (m + 2)) = (1 - α) * 1 := by
      simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring
    rw [e]; constructor <;> nlinarith

private theorem othersExpGain_zero (α γ : ℝ) : othersExpGain α γ .zero = (1 - α) * 1 := by
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]; ring

private theorem othersExpGain_tie (α γ : ℝ) :
    othersExpGain α γ .tie = (1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1 := by
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]; ring

private theorem othersExpGain_lead (α γ : ℝ) (n : ℕ) : othersExpGain α γ (.lead n) = 0 := by
  rcases n with _ | _ | n <;> simp [othersExpGain, outcomeSum, othersGain]

private theorem othersExpGain_lead_bound (α γ : ℝ) (m : ℕ) :
    0 ≤ othersExpGain α γ (.lead m) ∧ othersExpGain α γ (.lead m) ≤ 2 := by
  rw [othersExpGain_lead]; norm_num

/-- Dominated convergence for `Σ_s y n s · g s` when the `y n` are uniformly geometrically
dominated on the leads and `g` is bounded on the leads. -/
private theorem tendsto_stateSum_mul {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {y : ℕ → State → ℝ}
    {ν : State → ℝ} (hy : ∀ s, Tendsto (fun n => y n s) atTop (𝓝 (ν s))) {C : ℝ}
    (hb : ∀ n m, |y n (.lead m)| ≤ C * (α / (1 - α)) ^ m) (g : State → ℝ) {G : ℝ}
    (hg : ∀ m, |g (.lead m)| ≤ G) :
    Tendsto (fun n => stateSum (fun s => y n s * g s)) atTop
      (𝓝 (stateSum (fun s => ν s * g s))) := by
  unfold stateSum
  refine (((hy .zero).mul_const _).add ((hy .tie).mul_const _)).add ?_
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => C * (α / (1 - α)) ^ m * G)
    (((summable_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)).mul_left C).mul_right G)
    (fun m => (hy (.lead m)).mul_const _) (Eventually.of_forall fun n m => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hb n m) (hg m) (abs_nonneg _) ((abs_nonneg _).trans (hb n m))

private theorem cesaro_zero_abs_le {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (n m : ℕ) :
    |cesaro α γ (delta .zero) n (.lead m)| ≤ 1 * (α / (1 - α)) ^ m := by
  rw [abs_of_nonneg (cesaro_nonneg h0 h1 (isDist_delta _) n _), one_mul]
  exact cesaro_le (pow_nonneg (ratio_nonneg h0 h1) m) (fun k => distN_zero_lead_le α γ h0 h1 k m) n

private theorem distN_zero_mul_summable {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (k : ℕ)
    {g : State → ℝ} (hg : ∀ m, 0 ≤ g (.lead m) ∧ g (.lead m) ≤ 2) :
    Summable (fun m : ℕ => distN α γ (delta .zero) k (.lead m) * g (.lead m)) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg
    ((isDist_distN α γ h0 h1 _ (isDist_delta _) k).nonneg _) (hg m).1) (fun m => ?_)
    ((summable_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)).mul_right 2)
  exact mul_le_mul (distN_zero_lead_le α γ h0 h1 k m) (hg m).2 (hg m).1
    (pow_nonneg (ratio_nonneg h0 h1) m)

/-- The time-averaged pool gain is the expected pool gain under the Cesàro average. -/
theorem BitcoinSelfishErgodic.avgPoolGain_eq (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishErgodic.avgPoolGain α γ n =
      BitcoinSelfishErgodic.expPoolGain α γ
        (BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta .zero) n) := by
  unfold avgPoolGain expPoolGain
  have e : (fun s => cesaro α γ (delta .zero) n s * poolExpGain α γ s) =
      fun s => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n,
        (distN α γ (delta .zero) k s * poolExpGain α γ s) := by
    funext s; unfold cesaro; rw [mul_assoc, Finset.sum_mul]
  rw [e, stateSum_const_mul,
    stateSum_finsetSum (f := fun k s => distN α γ (delta .zero) k s * poolExpGain α γ s)
      (fun k _ => distN_zero_mul_summable h0 h1 k (poolExpGain_lead_bound h0 h1))]

/-- The time-averaged honest gain is the expected honest gain under the Cesàro average. -/
theorem BitcoinSelfishErgodic.avgOthersGain_eq (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishErgodic.avgOthersGain α γ n =
      BitcoinSelfishErgodic.expOthersGain α γ
        (BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta .zero) n) := by
  unfold avgOthersGain expOthersGain
  have e : (fun s => cesaro α γ (delta .zero) n s * othersExpGain α γ s) =
      fun s => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n,
        (distN α γ (delta .zero) k s * othersExpGain α γ s) := by
    funext s; unfold cesaro; rw [mul_assoc, Finset.sum_mul]
  rw [e, stateSum_const_mul,
    stateSum_finsetSum (f := fun k s => distN α γ (delta .zero) k s * othersExpGain α γ s)
      (fun k _ => distN_zero_mul_summable h0 h1 k (othersExpGain_lead_bound α γ))]

/-- **The pool's revenue rate is a long-run average.** The expected number of blocks per step
credited to the pool over the first `n` steps of the chain started at `zero` converges to the
paper's stationary revenue rate `poolRevenue α γ` (eq. (8)). -/
theorem BitcoinSelfishErgodic.avgPoolGain_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgPoolGain α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.poolRevenue α γ)) := by
  have e : avgPoolGain α γ = fun n => expPoolGain α γ (cesaro α γ (delta .zero) n) :=
    funext (avgPoolGain_eq α γ h0 h1)
  rw [e]
  unfold expPoolGain poolRevenue
  exact tendsto_stateSum_mul h0 h1 (fun s => cesaro_zero_tendsto α γ h0 h1 s)
    (cesaro_zero_abs_le h0 h1) (poolExpGain α γ) (G := 2) (fun m => by
      rw [abs_of_nonneg (poolExpGain_lead_bound h0 h1 m).1]; exact (poolExpGain_lead_bound h0 h1 m).2)

/-- **The honest miners' revenue rate is a long-run average.** -/
theorem BitcoinSelfishErgodic.avgOthersGain_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgOthersGain α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.othersRevenue α γ)) := by
  have e : avgOthersGain α γ = fun n => expOthersGain α γ (cesaro α γ (delta .zero) n) :=
    funext (avgOthersGain_eq α γ h0 h1)
  rw [e]
  unfold expOthersGain othersRevenue
  exact tendsto_stateSum_mul h0 h1 (fun s => cesaro_zero_tendsto α γ h0 h1 s)
    (cesaro_zero_abs_le h0 h1) (othersExpGain α γ) (G := 2) (fun m => by
      rw [abs_of_nonneg (othersExpGain_lead_bound α γ m).1]
      exact (othersExpGain_lead_bound α γ m).2)

private theorem denom_pos_aux {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 < denom α := by
  unfold denom
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - 2 * α) (by linarith : (0:ℝ) < 1 + α),
    mul_nonneg h0.le (sq_nonneg (α - 1 / 2))]

/-- The total stationary revenue rate is positive (for `0 ≤ γ ≤ 1`). -/
private theorem revenue_sum_pos {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) : 0 < poolRevenue α γ + othersRevenue α γ := by
  have hp : 0 ≤ poolRevenue α γ := by
    have hg : ∀ s, 0 ≤ poolExpGain α γ s := by
      intro s
      rcases s with _ | _ | m
      · rw [poolExpGain_zero]
      · rw [poolExpGain_tie]; nlinarith
      · exact (poolExpGain_lead_bound h0 h1 m).1
    have : ∀ s, 0 ≤ stationary α s * poolExpGain α γ s :=
      fun s => mul_nonneg (stationary_nonneg α h0 h1 s) (hg s)
    unfold poolRevenue stateSum
    exact add_nonneg (add_nonneg (this _) (this _)) (tsum_nonneg fun n => this _)
  have ho : stationary α .zero * ((1 - α) * 1) ≤ othersRevenue α γ := by
    unfold othersRevenue stateSum
    simp only [othersExpGain_zero, othersExpGain_lead, mul_zero, tsum_zero, add_zero]
    have := mul_nonneg (stationary_nonneg α h0 h1 .tie)
      (by rw [othersExpGain_tie]; nlinarith : 0 ≤ othersExpGain α γ .tie)
    linarith
  have hz : 0 < stationary α .zero := by
    simp only [stationary]
    exact div_pos (by linarith) (denom_pos_aux h0 h1)
  have : 0 < stationary α .zero * ((1 - α) * 1) := by
    apply mul_pos hz; linarith
  linarith

/-- **The relative revenue is a long-run average.** The pool's time-averaged relative revenue
over the first `n` steps of the chain started at `zero` converges to the paper's
`relativeRevenue α γ` (eq. (10)). -/
theorem BitcoinSelfishErgodic.avgRelativeRevenue_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgRelativeRevenue α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.relativeRevenue α γ)) := by
  unfold avgRelativeRevenue relativeRevenue
  exact (avgPoolGain_tendsto α γ h0 h1).div
    ((avgPoolGain_tendsto α γ h0 h1).add (avgOthersGain_tendsto α γ h0 h1))
    (revenue_sum_pos h0 h1 hγ0 hγ1).ne'

/-- **The profitability threshold is a long-run statement.** If `α > (1 - γ) / (3 - 2γ)`, then
for all sufficiently long horizons the pool's time-averaged relative revenue exceeds its hashrate
share `α`. -/
theorem BitcoinSelfishErgodic.avgRelativeRevenue_eventually_gt (α γ : ℝ) (h0 : 0 < α)
    (h1 : α < 1 / 2) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hT : α > BitcoinSelfishMining.profitThreshold γ) :
    ∀ᶠ n in Filter.atTop, α < BitcoinSelfishErgodic.avgRelativeRevenue α γ n :=
  (avgRelativeRevenue_tendsto α γ h0 h1 hγ0 hγ1).eventually_const_lt
    ((threshold α γ h0 h1 hγ0 hγ1).2 hT)

/-! ## Convergence of the `n`-step distributions themselves

The chain started at `zero` regenerates at each return to `zero`. Writing `u n = returnProb n`
for the renewal sequence, `g n = taboo zero n` for the taboo sub-distributions and
`f n = firstPassage zero n` for the first-return distribution, the last-exit decomposition
`distN n δ₀ = Σ_{k ≤ n} u k · g (n - k)` and the renewal equation `u (n+1) = Σ_{k ≤ n} f k · u (n-k)`
are proved by induction. A subsequence (Erdős–Feller–Pollard type) argument then shows that the
renewal sequence converges (aperiodicity comes from `f 0 = 1 - α > 0`); the Cesàro limit
identifies the limit as `stationary α zero`, and the last-exit decomposition transfers the
convergence to every state. A first-passage decomposition does the same for every initial state. -/

private theorem dist_add (α γ : ℝ) (μ ν : State → ℝ) (s : State) :
    dist α γ (fun t => μ t + ν t) s = dist α γ μ s + dist α γ ν s := by
  rcases s with _ | _ | _ | _ | n <;>
    simp only [zero_add, BitcoinSelfishErgodic.dist_zero, dist_tie, dist_lead_zero, dist_lead_one,
      dist_lead_succ] <;> ring

private theorem kill_zero (μ : State → ℝ) : kill μ .zero = 0 := by simp [kill]

private theorem kill_tie (μ : State → ℝ) : kill μ .tie = μ .tie := by simp [kill]

private theorem kill_lead (μ : State → ℝ) (n : ℕ) : kill μ (.lead n) = μ (.lead n) := by
  simp [kill]

/-- `dist (taboo n) s = taboo (n+1) s + [s = zero] · firstPassage n`. -/
private theorem dist_taboo (α γ : ℝ) (t : State) (n : ℕ) (s : State) :
    dist α γ (taboo α γ t n) s =
      taboo α γ t (n + 1) s + (if s = .zero then firstPassage α γ t n else 0) := by
  show dist α γ (taboo α γ t n) s = kill (dist α γ (taboo α γ t n)) s + _
  unfold kill firstPassage
  split_ifs with h
  · subst h; ring
  · ring

private theorem taboo_succ_zero (α γ : ℝ) (t : State) (n : ℕ) :
    taboo α γ t (n + 1) .zero = 0 :=
  kill_zero _

private theorem taboo_nonneg {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (t : State) (n : ℕ)
    (s : State) : 0 ≤ taboo α γ t n s := by
  induction n generalizing s with
  | zero => exact (isDist_delta t).nonneg s
  | succ n ih =>
    show 0 ≤ kill (dist α γ (taboo α γ t n)) s
    unfold kill
    split_ifs
    · exact le_rfl
    · exact dist_nonneg α γ h0.le (by linarith) _ ih s

private theorem taboo_summable (α γ : ℝ) (t : State) (n : ℕ) :
    Summable (fun m : ℕ => taboo α γ t n (.lead m)) := by
  induction n with
  | zero => exact delta_lead_summable t
  | succ n ih =>
    show Summable (fun m => kill (dist α γ (taboo α γ t n)) (.lead m))
    simp only [kill_lead]
    exact dist_summable ih

private theorem stateSum_kill (μ : State → ℝ) : stateSum (kill μ) = stateSum μ - μ .zero := by
  unfold stateSum
  simp only [kill_zero, kill_tie, kill_lead]
  ring

private theorem noPassage_succ (α γ : ℝ) (t : State) (n : ℕ) :
    noPassage α γ t (n + 1) = noPassage α γ t n - firstPassage α γ t n := by
  unfold noPassage firstPassage
  show stateSum (kill (dist α γ (taboo α γ t n))) = _
  rw [stateSum_kill, dist_mass α γ _ (taboo_summable α γ t n)]

private theorem noPassage_eq (α γ : ℝ) (t : State) (n : ℕ) :
    noPassage α γ t n = 1 - ∑ k ∈ Finset.range n, firstPassage α γ t k := by
  induction n with
  | zero => simp [noPassage, (isDist_delta t).mass, taboo]
  | succ n ih => rw [noPassage_succ, ih, Finset.sum_range_succ]; ring

private theorem firstPassage_nonneg {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (t : State) (n : ℕ) :
    0 ≤ firstPassage α γ t n :=
  dist_nonneg α γ h0.le (by linarith) _ (taboo_nonneg h0 h1 t n) .zero

private theorem noPassage_nonneg {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (t : State) (n : ℕ) :
    0 ≤ noPassage α γ t n := by
  unfold noPassage stateSum
  have := taboo_nonneg (α := α) (γ := γ) h0 h1 t n
  exact add_nonneg (add_nonneg (this _) (this _)) (tsum_nonneg fun m => this _)

private theorem firstPassage_sum_le {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (t : State) (n : ℕ) :
    ∑ k ∈ Finset.range n, firstPassage α γ t k ≤ 1 := by
  have := noPassage_nonneg (α := α) (γ := γ) h0 h1 t n
  rw [noPassage_eq] at this
  linarith

private theorem taboo_le_noPassage {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (t : State) (n : ℕ)
    (s : State) : taboo α γ t n s ≤ noPassage α γ t n := by
  unfold noPassage stateSum
  have hn := taboo_nonneg (α := α) (γ := γ) h0 h1 t n
  have hT : 0 ≤ ∑' m : ℕ, taboo α γ t n (.lead m) := tsum_nonneg (fun m => hn _)
  rcases s with _ | _ | m
  · linarith [hn State.tie]
  · linarith [hn State.zero]
  · have := (taboo_summable α γ t n).le_tsum m (fun j _ => hn _)
    linarith [hn State.zero, hn State.tie]

private theorem taboo_le_one {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (t : State) (n : ℕ)
    (s : State) : taboo α γ t n s ≤ 1 := by
  have := noPassage_eq α γ t n
  have h2 := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range n) =>
    firstPassage_nonneg (α := α) (γ := γ) h0 h1 t k)
  linarith [taboo_le_noPassage (α := α) (γ := γ) h0 h1 t n s]

/-- The first return to `zero` happens at time `1` with probability `1 - α`. -/
theorem BitcoinSelfishErgodic.firstReturn_zero (α γ : ℝ) :
    BitcoinSelfishErgodic.firstPassage α γ .zero 0 = 1 - α := by
  show dist α γ (delta .zero) .zero = _
  rw [BitcoinSelfishErgodic.dist_zero]
  simp [delta]

/-- **Last-exit decomposition.** For the chain started at `zero`, decomposing according to the
last visit to `zero` up to time `n`:
`P(X_n = s) = Σ_{k ≤ n} P(X_k = zero) · P(X_{n-k} = s, no return to zero in between)`. -/
theorem BitcoinSelfishErgodic.last_exit (α γ : ℝ) (n : ℕ) (s : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta .zero) n s =
      ∑ k ∈ Finset.range (n + 1),
        BitcoinSelfishErgodic.returnProb α γ k * BitcoinSelfishErgodic.taboo α γ .zero (n - k) s := by
  -- the inductive step, with the extra term at `zero`
  have step : ∀ n, (∀ s, distN α γ (delta .zero) n s =
      ∑ k ∈ Finset.range (n + 1), returnProb α γ k * taboo α γ .zero (n - k) s) → ∀ s,
      distN α γ (delta .zero) (n + 1) s =
        ∑ k ∈ Finset.range (n + 1), returnProb α γ k * taboo α γ .zero (n + 1 - k) s
          + (if s = .zero then
              ∑ k ∈ Finset.range (n + 1), returnProb α γ k * firstPassage α γ .zero (n - k)
            else 0) := by
    intro n ih s
    have e : distN α γ (delta .zero) n = fun s =>
        ∑ k ∈ Finset.range (n + 1), returnProb α γ k * taboo α γ .zero (n - k) s := funext ih
    show dist α γ (distN α γ (delta .zero) n) s = _
    rw [e, dist_finsetSum]
    simp only [dist_const_mul, dist_taboo]
    by_cases h : s = .zero
    · subst h
      simp [mul_add, Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k hk => by
        rw [Finset.mem_range] at hk
        rw [show n - k + 1 = n + 1 - k by omega])
    · simp [h]
      exact Finset.sum_congr rfl (fun k hk => by
        rw [Finset.mem_range] at hk
        rw [show n - k + 1 = n + 1 - k by omega])
  induction n generalizing s with
  | zero =>
    simp [returnProb, taboo, delta, distN]
  | succ n ih =>
    have hren : returnProb α γ (n + 1) =
        ∑ k ∈ Finset.range (n + 1), returnProb α γ k * firstPassage α γ .zero (n - k) := by
      have := step n ih .zero
      rw [if_pos rfl, Finset.sum_eq_zero (fun k hk => by
        rw [Finset.mem_range] at hk
        rw [show n + 1 - k = (n - k) + 1 by omega, taboo_succ_zero, mul_zero]), zero_add] at this
      exact this
    rw [step n ih s, Finset.sum_range_succ _ (n + 1), Nat.sub_self]
    show _ = _ + returnProb α γ (n + 1) * (if s = .zero then 1 else 0)
    rw [hren]
    split_ifs <;> ring

/-- Reflection of a convolution sum. -/
private theorem conv_reflect (n : ℕ) (a b : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), a k * b (n - k) = ∑ k ∈ Finset.range (n + 1), a (n - k) * b k := by
  rw [← Finset.sum_range_reflect (fun k => a (n - k) * b k) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega]

/-- **Renewal equation.** `P(X_{n+1} = zero) = Σ_{k ≤ n} f k · P(X_{n-k} = zero)` where `f k` is
the probability that the first return to `zero` happens at time `k + 1`. -/
theorem BitcoinSelfishErgodic.renewal_equation (α γ : ℝ) (n : ℕ) :
    BitcoinSelfishErgodic.returnProb α γ (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        BitcoinSelfishErgodic.firstPassage α γ .zero k * BitcoinSelfishErgodic.returnProb α γ (n - k) := by
  have key : ∀ n, returnProb α γ (n + 1) =
      ∑ k ∈ Finset.range (n + 1), returnProb α γ k * firstPassage α γ .zero (n - k) := by
    intro n
    have e : distN α γ (delta .zero) n = fun s =>
        ∑ k ∈ Finset.range (n + 1), returnProb α γ k * taboo α γ .zero (n - k) s :=
      funext (last_exit α γ n)
    show dist α γ (distN α γ (delta .zero) n) .zero = _
    rw [e, dist_finsetSum]
    simp only [dist_const_mul, dist_taboo, taboo_succ_zero, zero_add, ite_true]
  rw [key n, conv_reflect n (returnProb α γ) (firstPassage α γ .zero)]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The mass identity `Σ_{k ≤ n} P(X_{n-k} = zero) · P(no return in `1..k`) = 1`. -/
private theorem mass_identity {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), returnProb α γ (n - k) * noPassage α γ .zero k = 1 := by
  have hx := (isDist_distN α γ h0 h1 _ (isDist_delta .zero) n).mass
  have e : distN α γ (delta .zero) n = fun s =>
      ∑ k ∈ Finset.range (n + 1), returnProb α γ k * taboo α γ .zero (n - k) s :=
    funext (last_exit α γ n)
  rw [e, stateSum_finsetSum (f := fun k s => returnProb α γ k * taboo α γ .zero (n - k) s)
    (fun k _ => (taboo_summable α γ .zero (n - k)).mul_left _)] at hx
  simp only [stateSum_const_mul] at hx
  rw [← hx, ← conv_reflect n (returnProb α γ) (noPassage α γ .zero)]
  rfl
