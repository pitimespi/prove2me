import Definitions.Def_BitcoinSelfishMining

open BitcoinSelfishMining

/-! Helper lemmas. -/

private theorem denom_pos_aux {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 < denom α := by
  unfold denom
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - 2 * α) (by linarith : (0:ℝ) < 1 + α),
    mul_nonneg h0.le (sq_nonneg (α - 1 / 2))]

private theorem one_sub_pos {α : ℝ} (h1 : α < 1 / 2) : 0 < 1 - α := by linarith

private theorem one_sub_two_pos {α : ℝ} (h1 : α < 1 / 2) : 0 < 1 - 2 * α := by linarith

private theorem ratio_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 ≤ α / (1 - α) :=
  div_nonneg h0.le (one_sub_pos h1).le

private theorem ratio_lt_one {α : ℝ} (h1 : α < 1 / 2) : α / (1 - α) < 1 :=
  (div_lt_one (one_sub_pos h1)).mpr (by linarith)

private theorem p1_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    0 ≤ (α - 2 * α ^ 2) / denom α := by
  apply div_nonneg _ (denom_pos_aux h0 h1).le
  nlinarith

/-- Summability of the lead probabilities `n ↦ p_{n+1}`. -/
private theorem lead_summable {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    Summable (fun n : ℕ => stationary α (.lead n)) := by
  simp only [stationary]
  exact (summable_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)).mul_right _

/-- `∑ n, r^n p₁ = p₁ (1 - α) / (1 - 2α)`. -/
private theorem lead_tsum {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∑' n : ℕ, stationary α (.lead n) = (α - 2 * α ^ 2) / denom α * (1 - α) / (1 - 2 * α) := by
  simp only [stationary]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)]
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  have h2' := (one_sub_two_pos h1).ne'
  field_simp
  ring

private theorem poolExpGain_zero (α γ : ℝ) : poolExpGain α γ .zero = 0 := by
  simp [poolExpGain, outcomeSum, poolGain]

private theorem poolExpGain_tie (α γ : ℝ) :
    poolExpGain α γ .tie = α * 2 + γ * (1 - α) * 1 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

private theorem poolExpGain_lead0 (α γ : ℝ) : poolExpGain α γ (.lead 0) = 0 := by
  simp [poolExpGain, outcomeSum, poolGain]

private theorem poolExpGain_lead1 (α γ : ℝ) : poolExpGain α γ (.lead 1) = (1 - α) * 2 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

private theorem poolExpGain_lead2 (α γ : ℝ) (n : ℕ) :
    poolExpGain α γ (.lead (n + 2)) = (1 - α) * 1 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

private theorem othersExpGain_zero (α γ : ℝ) : othersExpGain α γ .zero = (1 - α) * 1 := by
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]; ring

private theorem othersExpGain_tie (α γ : ℝ) :
    othersExpGain α γ .tie = (1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1 := by
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]; ring

private theorem othersExpGain_lead (α γ : ℝ) (n : ℕ) : othersExpGain α γ (.lead n) = 0 := by
  rcases n with _ | _ | n <;> simp [othersExpGain, outcomeSum, othersGain]

/-! Public theorems. -/

/-- The common denominator `2α³ - 4α² + 1` of the stationary probabilities is positive for
`0 < α < 1/2`. -/
theorem BitcoinSelfishMining.denominator_pos (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    0 < 2 * α ^ 3 - 4 * α ^ 2 + 1 := by
  exact denom_pos_aux h0 h1

/-- All stationary probabilities are nonnegative for `0 < α < 1/2`. -/
theorem BitcoinSelfishMining.stationary_nonneg (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) : 0 ≤ BitcoinSelfishMining.stationary α s := by
  have hD := denom_pos_aux h0 h1
  rcases s with _ | _ | n
  · simp only [stationary]
    exact div_nonneg (by linarith) hD.le
  · simp only [stationary]
    exact div_nonneg (mul_nonneg (one_sub_pos h1).le (by nlinarith [mul_pos h0 (one_sub_two_pos h1)]))
      hD.le
  · simp only [stationary]
    exact mul_nonneg (pow_nonneg (ratio_nonneg h0 h1) n) (p1_nonneg h0 h1)

/-- Balance at state `0`: inflow from `0` (honest block, `1 - α`), from the tie `0'` (every
outcome) and from lead `2` (honest block, `1 - α`). -/
theorem BitcoinSelfishMining.balance_zero (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α .zero =
      (1 - α) * BitcoinSelfishMining.stationary α .zero
        + BitcoinSelfishMining.stationary α .tie
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead 1) := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  simp only [stationary]
  field_simp
  ring

/-- Balance at the tie `0'`: inflow from lead `1` on an honest block. -/
theorem BitcoinSelfishMining.balance_tie (α : ℝ) (_h0 : 0 < α) (_h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α .tie =
      (1 - α) * BitcoinSelfishMining.stationary α (.lead 0) := by
  simp only [stationary]
  ring

/-- Balance at lead `1`: inflow from `0` on a pool block. -/
theorem BitcoinSelfishMining.balance_one (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α (.lead 0) =
      α * BitcoinSelfishMining.stationary α .zero := by
  have hD := (denom_pos_aux h0 h1).ne'
  simp only [stationary]
  field_simp

/-- Balance at lead `2`: inflow from lead `1` (pool block) and lead `3` (honest block). -/
theorem BitcoinSelfishMining.balance_two (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α (.lead 1) =
      α * BitcoinSelfishMining.stationary α (.lead 0)
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead 2) := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  simp only [stationary]
  field_simp
  ring

/-- Balance at lead `k = n + 3 ≥ 3`: inflow from lead `k - 1` (pool block) and lead `k + 1`
(honest block). -/
theorem BitcoinSelfishMining.balance_lead (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishMining.stationary α (.lead (n + 2)) =
      α * BitcoinSelfishMining.stationary α (.lead (n + 1))
        + (1 - α) * BitcoinSelfishMining.stationary α (.lead (n + 3)) := by
  have h1' := (one_sub_pos h1).ne'
  have key : α / (1 - α) = α + (1 - α) * (α / (1 - α)) ^ 2 := by
    field_simp
    ring
  simp only [stationary]
  have e2 : (α / (1 - α)) ^ (n + 2) = (α / (1 - α)) ^ (n + 1) * (α / (1 - α)) := by ring
  have e3 : (α / (1 - α)) ^ (n + 3) = (α / (1 - α)) ^ (n + 1) * (α / (1 - α)) ^ 2 := by ring
  rw [e2, e3]
  linear_combination ((α / (1 - α)) ^ (n + 1) * ((α - 2 * α ^ 2) / denom α)) * key

/-- `P` is a stochastic matrix: from every state the transition probabilities sum to one
(the three outcome probabilities `α + (1-α)γ + (1-α)(1-γ)` add up to `1`). -/
theorem BitcoinSelfishMining.P_row_sum (α γ : ℝ) (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stateSum (fun t => BitcoinSelfishMining.P α γ s t) = 1 := by
  unfold stateSum
  rcases s with _ | _ | _ | _ | k
  · rw [tsum_eq_single 0 ?_]
    · simp [P, outcomeSum, step, outcomeProb]; ring
    · intro b hb
      rcases b with _ | b
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
  · rw [tsum_eq_single 0 ?_]
    · simp [P, outcomeSum, step, outcomeProb]; ring
    · intro b _
      simp [P, outcomeSum, step]
  · rw [tsum_eq_single 1 ?_]
    · simp [P, outcomeSum, step, outcomeProb]; ring
    · intro b hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
  · rw [tsum_eq_single 2 ?_]
    · simp [P, outcomeSum, step, outcomeProb]; ring
    · intro b hb
      rcases b with _ | _ | _ | b
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
  · rw [tsum_eq_sum (s := {k + 1, k + 3}) ?_, Finset.sum_pair (by omega)]
    · simp [P, outcomeSum, step, outcomeProb]; ring
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      have h1' : b ≠ k + 1 := hb.1
      have h3' : b ≠ k + 3 := hb.2
      simp [P, outcomeSum, step, Ne.symm h1', Ne.symm h3']

/-- The paper's distribution is stationary for the chain: at every state `s`,
`p_s = Σ_t p_t · P(t → s)`, the sum running over all states (`stateSum`). -/
theorem BitcoinSelfishMining.stationary_balance (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stationary α s =
      BitcoinSelfishMining.stateSum
        (fun t => BitcoinSelfishMining.stationary α t * BitcoinSelfishMining.P α γ t s) := by
  unfold stateSum
  rcases s with _ | _ | _ | _ | _ | k
  · -- state 0: inflow from 0, 0' and lead 2
    rw [tsum_eq_single 1 ?_]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      linear_combination balance_zero α h0 h1
    · intro b hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
  · -- the tie: inflow from lead 1
    rw [tsum_eq_single 0 ?_]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      linear_combination balance_tie α h0 h1
    · intro b hb
      rcases b with _ | _ | b
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
  · -- lead 1: inflow from 0
    rw [tsum_eq_single 0 ?_]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      linear_combination balance_one α h0 h1
    · intro b hb
      rcases b with _ | _ | b
      · exact absurd rfl hb
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
  · -- lead 2: inflow from lead 1 and lead 3
    rw [tsum_eq_sum (s := {0, 2}) ?_, Finset.sum_pair (by norm_num)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      linear_combination balance_two α h0 h1
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · exact absurd rfl hb.1
      · simp [P, outcomeSum, step]
      · have : b ≠ 0 := by omega
        simp [P, outcomeSum, step, this]
  · -- lead 3: inflow from lead 2 and lead 4
    rw [tsum_eq_sum (s := {1, 3}) ?_, Finset.sum_pair (by norm_num)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      have := balance_lead α h0 h1 0
      simp only [Nat.zero_add] at this
      linear_combination this
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · exact absurd rfl hb.1
      · have h1' : b ≠ 1 := by omega
        simp [P, outcomeSum, step, h1']
  · -- lead k + 4 ≥ 4: inflow from lead k + 3 and lead k + 5
    rw [tsum_eq_sum (s := {k + 2, k + 4}) ?_, Finset.sum_pair (by omega)]
    · simp only [P, outcomeSum, step, outcomeProb]
      simp
      have := balance_lead α h0 h1 (k + 1)
      simp only [add_assoc, Nat.reduceAdd] at this
      linear_combination this
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      rcases b with _ | _ | b
      · simp [P, outcomeSum, step]
      · simp [P, outcomeSum, step]
      · have h1' : b ≠ k := by omega
        have h0' : b ≠ k + 2 := by omega
        simp [P, outcomeSum, step, h1', h0']

/-- The geometric tail `Σ_{k ≥ 3} p_k = p₁ (α/(1-α))² (1-α)/(1-2α)`. -/
theorem BitcoinSelfishMining.tail_sum (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∑' n : ℕ, BitcoinSelfishMining.stationary α (.lead (n + 2)) =
      BitcoinSelfishMining.stationary α (.lead 0) * (α / (1 - α)) ^ 2 * (1 - α) / (1 - 2 * α) := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  have h2' := (one_sub_two_pos h1).ne'
  simp only [stationary, pow_zero, one_mul]
  have : (fun n : ℕ => (α / (1 - α)) ^ (n + 2) * ((α - 2 * α ^ 2) / denom α)) =
      fun n : ℕ => ((α / (1 - α)) ^ 2 * ((α - 2 * α ^ 2) / denom α)) * (α / (1 - α)) ^ n := by
    funext n; ring
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)]
  field_simp
  ring

/-- The stationary distribution has total mass one: `p₀ + p₀' + Σ_{k ≥ 1} p_k = 1`. -/
theorem BitcoinSelfishMining.total_mass (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stateSum (BitcoinSelfishMining.stationary α) = 1 := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  have h2' := (one_sub_two_pos h1).ne'
  have h2'' : 1 - α * 2 ≠ 0 := by rwa [mul_comm]
  unfold stateSum
  rw [lead_tsum h0 h1]
  simp only [stationary]
  field_simp
  unfold denom
  ring

/-- The pool's revenue rate is the paper's eq. (8):
`r_pool = p₀' (α·2 + γ(1-α)·1) + p₂ (1-α)·2 + (Σ_{k≥3} p_k) (1-α)·1`. -/
theorem BitcoinSelfishMining.pool_revenue_eq (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.poolRevenue α γ =
      BitcoinSelfishMining.stationary α .tie * (α * 2 + γ * (1 - α) * 1)
        + BitcoinSelfishMining.stationary α (.lead 1) * ((1 - α) * 2)
        + (∑' n : ℕ, BitcoinSelfishMining.stationary α (.lead (n + 2))) * ((1 - α) * 1) := by
  unfold poolRevenue stateSum
  have hs : Summable (fun n : ℕ => stationary α (.lead n) * poolExpGain α γ (.lead n)) := by
    rw [← summable_nat_add_iff 2]
    simp only [poolExpGain_lead2]
    exact ((summable_nat_add_iff 2).mpr (lead_summable h0 h1)).mul_right _
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [poolExpGain_zero, poolExpGain_tie, poolExpGain_lead0, poolExpGain_lead1, zero_add,
    poolExpGain_lead2, mul_zero]
  rw [tsum_mul_right]
  have e : (fun x : ℕ => stationary α (.lead (x + 1 + 1))) =
      fun n : ℕ => stationary α (.lead (n + 2)) := rfl
  rw [e]
  ring

/-- The honest miners' revenue rate is the paper's eq. (9):
`r_others = p₀' ((1-α)(1-γ)·2 + γ(1-α)·1) + p₀ (1-α)·1`. -/
theorem BitcoinSelfishMining.others_revenue_eq (α γ : ℝ) :
    BitcoinSelfishMining.othersRevenue α γ =
      BitcoinSelfishMining.stationary α .tie * ((1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1)
        + BitcoinSelfishMining.stationary α .zero * ((1 - α) * 1) := by
  unfold othersRevenue stateSum
  simp only [othersExpGain_zero, othersExpGain_tie, othersExpGain_lead, mul_zero, tsum_zero,
    add_zero]
  ring

/-- Closed form of the pool's revenue rate over the common denominator. -/
private theorem pool_revenue_closed (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    poolRevenue α γ =
      (α * (1 - α) ^ 2 * (4 * α + γ * (1 - 2 * α)) - α ^ 3) / denom α := by
  have hD := (denom_pos_aux h0 h1).ne'
  have h1' := (one_sub_pos h1).ne'
  have h2' := (one_sub_two_pos h1).ne'
  have h2'' : 1 - α * 2 ≠ 0 := by rwa [mul_comm]
  rw [pool_revenue_eq α γ h0 h1, tail_sum α h0 h1]
  simp only [stationary, pow_zero, one_mul, pow_one]
  field_simp
  ring

/-- Closed form of the honest miners' revenue rate over the common denominator. -/
private theorem others_revenue_closed (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    othersRevenue α γ =
      ((1 - α) ^ 2 * α * (1 - 2 * α) * (2 - γ) + (1 - 2 * α) * (1 - α)) / denom α := by
  have hD := (denom_pos_aux h0 h1).ne'
  rw [others_revenue_eq]
  simp only [stationary]
  field_simp
  ring

/-- The total revenue rate is `(1 - α(1 + (2-α)α)) / denom α`. -/
private theorem total_revenue_closed (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    poolRevenue α γ + othersRevenue α γ = (1 - α * (1 + (2 - α) * α)) / denom α := by
  rw [pool_revenue_closed α γ h0 h1, others_revenue_closed α γ h0 h1, ← add_div]
  congr 1
  ring

private theorem closed_denom_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) :
    0 < 1 - α * (1 + (2 - α) * α) := by
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - 2 * α) (by linarith : (0:ℝ) < 1 + α),
    pow_pos h0 3]

/-- The pool's relative revenue equals the paper's closed form (eq. (10)):
`R = (α(1-α)²(4α + γ(1-2α)) - α³) / (1 - α(1 + (2-α)α))`. -/
theorem BitcoinSelfishMining.relative_revenue (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α γ = BitcoinSelfishMining.closedForm α γ := by
  have hD := (denom_pos_aux h0 h1).ne'
  have hN := (closed_denom_pos h0 h1).ne'
  unfold relativeRevenue closedForm
  rw [total_revenue_closed α γ h0 h1, pool_revenue_closed α γ h0 h1, div_div_div_cancel_right₀ hD]

/-- The profitability threshold (eq. (11)): for `0 < α < 1/2` and `0 ≤ γ ≤ 1`, selfish mining
earns more than the pool's fair share `α` iff `α > (1 - γ) / (3 - 2γ)`. -/
theorem BitcoinSelfishMining.threshold (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    BitcoinSelfishMining.relativeRevenue α γ > α ↔ α > BitcoinSelfishMining.profitThreshold γ := by
  have hN := closed_denom_pos h0 h1
  have h3 : (0:ℝ) < 3 - 2 * γ := by linarith
  have hpos : 0 < α * (1 - α) ^ 2 := mul_pos h0 (pow_pos (one_sub_pos h1) 2)
  rw [relative_revenue α γ h0 h1, closedForm, profitThreshold, gt_iff_lt, gt_iff_lt, lt_div_iff₀ hN,
    div_lt_iff₀ h3]
  have key : α * (1 - α) ^ 2 * (4 * α + γ * (1 - 2 * α)) - α ^ 3 - α * (1 - α * (1 + (2 - α) * α))
      = (α * (1 - α) ^ 2) * (α * (3 - 2 * γ) - (1 - γ)) := by ring
  rw [← sub_pos, key, mul_pos_iff_of_pos_left hpos]
  exact sub_pos

/-- With `γ = 0` (honest miners never adopt the pool's block in a tie), selfish mining is
profitable iff `α > 1/3`. -/
theorem BitcoinSelfishMining.threshold_gamma_zero (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α 0 > α ↔ α > 1 / 3 := by
  rw [threshold α 0 h0 h1 le_rfl zero_le_one, profitThreshold]
  norm_num

/-- With `γ = 1` (honest miners always adopt the pool's block in a tie), selfish mining is
profitable for every pool size `0 < α < 1/2`. -/
theorem BitcoinSelfishMining.threshold_gamma_one (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α 1 > α := by
  rw [threshold α 1 h0 h1 zero_le_one le_rfl, profitThreshold]
  norm_num
  exact h0

