import Definitions.Def_BitcoinBackboneProb

open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

/-! ## Finite computations on one round -/

private theorem integral_pi_prod_ber (m : ℕ) (p : unitInterval) (g : Fin m → Bool → ℝ) :
    ∫ f : Fin m → Bool, ∏ i, g i (f i) ∂(Measure.pi fun _ => ber p) =
      ∏ i, ((p : ℝ) * g i true + (1 - (p : ℝ)) * g i false) := by
  rw [integral_fintype_prod_eq_prod]
  congr 1; ext i
  simp [ber, integral_bernoulliMeasure]

private theorem integral_pi_eval_ber (m : ℕ) (p : unitInterval) (j : Fin m) (g : Bool → ℝ) :
    ∫ f : Fin m → Bool, g (f j) ∂(Measure.pi fun _ => ber p) =
      (p : ℝ) * g true + (1 - (p : ℝ)) * g false := by
  have h := integral_pi_prod_ber m p (fun i b => if i = j then g b else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

private theorem honestCount_eq_zero_iff {n t : ℕ} (ρ : Round n t) :
    honestCount ρ = 0 ↔ ∀ i, ρ.1 i = false := by
  simp [honestCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

private theorem honestCount_eq_one_iff {n t : ℕ} (ρ : Round n t) (i : Fin n) :
    (∀ j, ρ.1 j = decide (j = i)) → honestCount ρ = 1 := by
  intro h
  unfold honestCount
  rw [Finset.card_eq_one]
  exact ⟨i, by ext j; simp [h j]⟩

private theorem roundY_real_eq {n t : ℕ} (ρ : Round n t) :
    (roundY ρ : ℝ) = ∑ i, ∏ j, (if ρ.1 j = decide (j = i) then (1 : ℝ) else 0) := by
  simp only [Finset.prod_boole, Finset.mem_univ, true_implies]
  rw [Finset.sum_boole]
  unfold roundY
  by_cases h : honestCount ρ = 1
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
    have hf : ∀ j, ρ.1 j = decide (j = a) := by
      intro j
      have := congrArg (fun s => j ∈ s) ha
      simp at this
      cases hj : ρ.1 j <;> simp_all
    have : (Finset.univ.filter fun i => ∀ j, ρ.1 j = decide (j = i)) = {a} := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi; have := (hi a).symm.trans (hf a); simpa [eq_comm] using this
      · rintro rfl; exact hf
    simp [h, this]
  · have : (Finset.univ.filter fun i => ∀ j, ρ.1 j = decide (j = i)) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hi; exact h (honestCount_eq_one_iff ρ i hi)
    simp [h, this]

private theorem roundX_real_eq {n t : ℕ} (ρ : Round n t) :
    (roundX ρ : ℝ) = 1 - ∏ i, (if ρ.1 i = false then (1 : ℝ) else 0) := by
  rw [Finset.prod_boole]
  unfold roundX
  have := honestCount_eq_zero_iff ρ
  by_cases h : honestCount ρ = 0
  · simp [h, this.1 h]
  · have h' : ¬ ∀ i, ρ.1 i = false := fun h'' => h (this.2 h'')
    simp [Nat.pos_of_ne_zero h, h']

private theorem advCount_real_eq {n t : ℕ} (ρ : Round n t) :
    (advCount ρ : ℝ) = ∑ j, (if ρ.2 j = true then (1 : ℝ) else 0) := by
  simp [advCount, Finset.sum_boole]

private theorem integral_round_fst (n t : ℕ) (p : unitInterval) (g : (Fin n → Bool) → ℝ) :
    ∫ ρ, g ρ.1 ∂(roundMeasure n t p) = ∫ f, g f ∂(Measure.pi fun _ => ber p) := by
  unfold roundMeasure
  rw [integral_fun_fst]; simp

private theorem integral_round_snd (n t : ℕ) (p : unitInterval) (g : (Fin t → Bool) → ℝ) :
    ∫ ρ, g ρ.2 ∂(roundMeasure n t p) = ∫ f, g f ∂(Measure.pi fun _ => ber p) := by
  unfold roundMeasure
  rw [integral_fun_snd]; simp

/-- `E[Y] = n p (1 - p)^(n - 1)` for one round: exactly one of `n` independent Bernoulli(`p`)
queries succeeds. -/
theorem BitcoinBackboneProb.integral_roundY (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (roundY ρ : ℝ) ∂(roundMeasure n t p) = n * p * (1 - (p : ℝ)) ^ (n - 1) := by
  simp_rw [roundY_real_eq]
  rw [integral_round_fst n t p (fun f => ∑ i, ∏ j, (if f j = decide (j = i) then (1 : ℝ) else 0))]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  rw [Finset.sum_congr rfl (fun i _ => integral_pi_prod_ber n p
    (fun j b => if b = decide (j = i) then (1 : ℝ) else 0))]
  have : ∀ i : Fin n, (∏ j : Fin n, ((p : ℝ) * (if true = decide (j = i) then 1 else 0) +
      (1 - (p : ℝ)) * (if false = decide (j = i) then 1 else 0))) = p * (1 - p) ^ (n - 1) := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [decide_true, if_true, mul_one]
    simp (config := {decide := true}) only [if_false]
    rw [Finset.prod_congr rfl (g := fun _ => 1 - (p : ℝ))]
    · simp [Finset.card_erase_of_mem]
    · intro j hj
      have : j ≠ i := Finset.ne_of_mem_erase hj
      simp [this]
  simp_rw [this]
  simp; ring

/-- `E[X] = 1 - (1 - p)^n` for one round: at least one honest query succeeds. -/
theorem BitcoinBackboneProb.integral_roundX (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (roundX ρ : ℝ) ∂(roundMeasure n t p) = 1 - (1 - (p : ℝ)) ^ n := by
  simp_rw [roundX_real_eq]
  rw [integral_round_fst n t p (fun f => 1 - ∏ i, (if f i = false then (1 : ℝ) else 0))]
  rw [integral_sub (integrable_const _) Integrable.of_finite,
    integral_pi_prod_ber n p (fun _ b => if b = false then (1 : ℝ) else 0)]
  simp

/-- `E[Z] = t p` for one round: the number of successful adversarial queries. -/
theorem BitcoinBackboneProb.integral_advCount (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (advCount ρ : ℝ) ∂(roundMeasure n t p) = t * p := by
  simp_rw [advCount_real_eq]
  rw [integral_round_snd n t p (fun f => ∑ j, (if f j = true then (1 : ℝ) else 0))]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  rw [Finset.sum_congr rfl (fun j _ => integral_pi_eval_ber t p j
    (fun b => if b = true then (1 : ℝ) else 0))]
  simp

private theorem integral_trace_eval (n t : ℕ) (p : unitInterval) (r : ℕ) (g : Round n t → ℝ) :
    ∫ ω, g (ω r) ∂(P n t p) = ∫ ρ, g ρ ∂(roundMeasure n t p) := by
  unfold P
  conv_rhs => rw [← Measure.infinitePi_map_eval (fun _ : ℕ => roundMeasure n t p) r]
  rw [integral_map (measurable_pi_apply r).aemeasurable (Measurable.of_discrete.aestronglyMeasurable)]

/-- The rounds of a trace are independent under `P n t p`. -/
theorem BitcoinBackboneProb.iIndepFun_rounds (n t : ℕ) (p : unitInterval) :
    ProbabilityTheory.iIndepFun (fun r (ω : Trace n t) => ω r) (P n t p) := by
  exact iIndepFun_infinitePi (X := fun _ ρ => ρ) (fun _ => measurable_id)

/-- Each round of a trace is distributed according to `roundMeasure n t p`. -/
theorem BitcoinBackboneProb.map_eval_P (n t : ℕ) (p : unitInterval) (r : ℕ) :
    (P n t p).map (fun ω => ω r) = roundMeasure n t p := by
  exact Measure.infinitePi_map_eval _ r

/-! ## Expectations of the trace variables -/

/-- `E[Y_r] = n p (1 - p)^(n - 1)` under the trace law. -/
theorem BitcoinBackboneProb.expect_Y (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Y ω r : ℝ) ∂(P n t p) = n * p * (1 - (p : ℝ)) ^ (n - 1) := by
  unfold Y
  rw [integral_trace_eval n t p r (fun ρ => (roundY ρ : ℝ))]
  exact integral_roundY n t p

/-- `E[X_r] = 1 - (1 - p)^n` under the trace law. -/
theorem BitcoinBackboneProb.expect_X (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (X ω r : ℝ) ∂(P n t p) = 1 - (1 - (p : ℝ)) ^ n := by
  unfold X
  rw [integral_trace_eval n t p r (fun ρ => (roundX ρ : ℝ))]
  exact integral_roundX n t p

/-- `E[Z_r] = t p` under the trace law. -/
theorem BitcoinBackboneProb.expect_Z (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) = t * p := by
  unfold Z
  rw [integral_trace_eval n t p r (fun ρ => (advCount ρ : ℝ))]
  exact integral_advCount n t p

/-- The honest-majority margin is `E[Y_r] - E[Z_r]`. -/
theorem BitcoinBackboneProb.expect_Y_sub_expect_Z (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Y ω r : ℝ) ∂(P n t p) - ∫ ω, (Z ω r : ℝ) ∂(P n t p) = margin n t p := by
  rw [expect_Y, expect_Z, margin]

/-- Honest majority with a gap: if `t ≤ (1 - δ) n` and `p n ≤ δ / 2`, then the margin is at least
`δ p n / 2` (using Bernoulli's inequality `(1 - p)^(n-1) ≥ 1 - (n - 1) p`). -/
theorem BitcoinBackboneProb.margin_ge_of_honest_majority (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) :
    δ * p * n / 2 ≤ margin n t p := by
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbern : 1 + ((n - 1 : ℕ) : ℝ) * (-(p : ℝ)) ≤ (1 + -(p : ℝ)) ^ (n - 1) :=
    one_add_mul_le_pow (by linarith) _
  have hcast : ((n - 1 : ℕ) : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · rw [Nat.cast_sub h]; simp
  have h1 : 1 - (n : ℝ) * p ≤ (1 - (p : ℝ)) ^ (n - 1) := by
    have : ((n - 1 : ℕ) : ℝ) * p ≤ n * p := mul_le_mul_of_nonneg_right hcast hp0
    simp only [← sub_eq_add_neg] at hbern
    nlinarith
  have hnp : (0 : ℝ) ≤ n * p := mul_nonneg hn hp0
  unfold margin
  have h2 : (n : ℝ) * p * (1 - (n : ℝ) * p) ≤ n * p * (1 - (p : ℝ)) ^ (n - 1) :=
    mul_le_mul_of_nonneg_left h1 hnp
  have h3 : (t : ℝ) * p ≤ (1 - δ) * n * p := mul_le_mul_of_nonneg_right ht hp0
  nlinarith

/-- Under the same honest-majority condition, `E[Z_r] + δ p n / 2 ≤ E[Y_r]`. -/
theorem BitcoinBackboneProb.expect_Z_add_le_expect_Y (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) + δ * p * n / 2 ≤ ∫ ω, (Y ω r : ℝ) ∂(P n t p) := by
  have := margin_ge_of_honest_majority n t p δ ht hp
  have h2 := expect_Y_sub_expect_Z n t p r
  linarith

/-- Under honest majority with `δ, p, n > 0`, `E[Z_r] < E[Y_r]`. -/
theorem BitcoinBackboneProb.expect_Z_lt_expect_Y (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (hδ : 0 < δ) (hn : 0 < n) (hp0 : 0 < (p : ℝ))
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) < ∫ ω, (Y ω r : ℝ) ∂(P n t p) := by
  have := expect_Z_add_le_expect_Y n t p δ ht hp r
  have hpos : 0 < δ * p * n / 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  linarith


private theorem advCount_le {n t : ℕ} (ρ : Round n t) : advCount ρ ≤ t := by
  unfold advCount
  exact (Finset.card_filter_le _ _).trans (by simp)

private theorem roundY_le_one {n t : ℕ} (ρ : Round n t) : roundY ρ ≤ 1 := by
  unfold roundY; split_ifs <;> simp

private theorem hoeffding_core (n t : ℕ) (p : unitInterval) (S T : Finset ℕ) (hTS : T ⊆ S)
    (j : ℕ) (ε : ℝ)
    (hεdef : ε = j + T.card * (n * p * (1 - (p : ℝ)) ^ (n - 1)) - S.card * (t * p))
    (hε : 0 ≤ ε) :
    (P n t p).real {ω | ∑ i ∈ T, Y ω i + j ≤ ∑ i ∈ S, Z ω i} ≤
      Real.exp (-2 * ε ^ 2 / (S.card * ((t : ℝ) + 1) ^ 2)) := by
  classical
  set y : ℝ := n * p * (1 - (p : ℝ)) ^ (n - 1) with hy
  set z : ℝ := t * p with hz
  let V : ℕ → Round n t → ℝ := fun i ρ => (advCount ρ : ℝ) - if i ∈ T then (roundY ρ : ℝ) else 0
  have hVint : ∀ i, ∫ ω, V i (ω i) ∂(P n t p) = z - if i ∈ T then y else 0 := by
    intro i
    rw [integral_trace_eval n t p i (V i)]
    simp only [V]
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_advCount]
    split_ifs
    · rw [integral_roundY]
    · simp [hz]
  let Xf : ℕ → Trace n t → ℝ := fun i ω => V i (ω i) - (z - if i ∈ T then y else 0)
  have hind : iIndepFun Xf (P n t p) :=
    iIndepFun_infinitePi (X := fun i ρ => V i ρ - (z - if i ∈ T then y else 0))
      (fun _ => Measurable.of_discrete)
  have hsub : ∀ i ∈ S, HasSubgaussianMGF (Xf i) ((‖(t : ℝ) - (-1)‖₊ / 2) ^ 2) (P n t p) := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc (X := fun ω => V i (ω i)) (μ := P n t p)
      (a := -1) (b := t) ((Measurable.of_discrete (f := V i)).comp (measurable_pi_apply i)).aemeasurable
      (ae_of_all _ (fun ω => by
        have h1 := advCount_le (ω i)
        have h2 := roundY_le_one (ω i)
        have h1' : (advCount (ω i) : ℝ) ≤ t := by exact_mod_cast h1
        have h2' : (roundY (ω i) : ℝ) ≤ 1 := by exact_mod_cast h2
        have h3 : (0 : ℝ) ≤ advCount (ω i) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ roundY (ω i) := Nat.cast_nonneg _
        simp only [V, Set.mem_Icc]
        split_ifs <;> constructor <;> linarith))
    rw [hVint i] at h
    exact h
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub hε
  have hset : {ω : Trace n t | ∑ i ∈ T, Y ω i + j ≤ ∑ i ∈ S, Z ω i} =
      {ω | ε ≤ ∑ i ∈ S, Xf i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Xf, V]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTS]
    simp only [Finset.sum_const, nsmul_eq_mul, hεdef]
    have : ∀ i, (advCount (ω i) : ℝ) = Z ω i := fun i => rfl
    have : ∀ i, (roundY (ω i) : ℝ) = Y ω i := fun i => rfl
    simp only [*]
    constructor
    · intro h
      have : ((∑ i ∈ T, Y ω i + j : ℕ) : ℝ) ≤ ((∑ i ∈ S, Z ω i : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith
    · intro h
      have : ((∑ i ∈ T, Y ω i + j : ℕ) : ℝ) ≤ ((∑ i ∈ S, Z ω i : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
  rw [hset]
  refine hH.trans (le_of_eq ?_)
  congr 1
  simp only [Finset.sum_const, nsmul_eq_mul]
  push_cast
  rw [sub_neg_eq_add, Real.norm_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos S.card with h | h
  · simp [h]
  · have : (0 : ℝ) < S.card := by exact_mod_cast h
    field_simp

/-! ## Per-window concentration (Hoeffding) -/

/-- Hoeffding's inequality for the typicality defect on arbitrary finite sets of rounds: with
`T ⊆ S`, the probability that the adversarial blocks of the rounds in `S` reach the number of
uniquely successful rounds in `T` plus a slack `j` is exponentially small in the gap
`ε = j + |T| E[Y] - |S| E[Z]`. -/
theorem BitcoinBackboneProb.sets_hoeffding (n t : ℕ) (p : unitInterval) (S T : Finset ℕ)
    (hTS : T ⊆ S) (j : ℕ)
    (hε : 0 ≤ (j : ℝ) + T.card * (n * p * (1 - (p : ℝ)) ^ (n - 1)) - S.card * (t * p)) :
    (P n t p).real {ω | ∑ i ∈ T, Y ω i + j ≤ ∑ i ∈ S, Z ω i} ≤
      Real.exp (-2 * ((j : ℝ) + T.card * (n * p * (1 - (p : ℝ)) ^ (n - 1)) - S.card * (t * p)) ^ 2
        / (S.card * ((t : ℝ) + 1) ^ 2)) := by
  exact hoeffding_core n t p S T hTS j _ rfl hε

/-- Hoeffding bound for one window `[a, a + k]`: typicality fails on it with probability at most
`exp (-2 ((k - 1) m - 2 t p)² / ((k + 1) (t + 1)²))`, where `m` is the honest-majority margin. -/
theorem BitcoinBackboneProb.window_bound (n t : ℕ) (p : unitInterval) (a k : ℕ) (hk1 : 1 ≤ k)
    (hk : 2 * t * (p : ℝ) ≤ ((k : ℝ) - 1) * margin n t p) :
    (P n t p).real {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤
      Real.exp (-2 * (((k : ℝ) - 1) * margin n t p - 2 * t * p) ^ 2 /
        (((k : ℝ) + 1) * ((t : ℝ) + 1) ^ 2)) := by
  have hS : ((Finset.Icc a (a + k)).card : ℝ) = (k : ℝ) + 1 := by
    rw [Nat.card_Icc]; push_cast [show a + k + 1 - a = k + 1 by omega]; ring
  have hT : ((Finset.Ioo a (a + k)).card : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.card_Ioo, show a + k - a - 1 = k - 1 by omega, Nat.cast_sub hk1]; simp
  have heq : (0 : ℝ) + ((Finset.Ioo a (a + k)).card : ℝ) * (n * p * (1 - (p : ℝ)) ^ (n - 1)) -
      ((Finset.Icc a (a + k)).card : ℝ) * (t * p) = ((k : ℝ) - 1) * margin n t p - 2 * t * p := by
    rw [hS, hT, margin]; ring
  have h := sets_hoeffding n t p (Finset.Icc a (a + k)) (Finset.Ioo a (a + k))
    Finset.Ioo_subset_Icc_self 0 (by push_cast; rw [heq]; linarith)
  simp only [add_zero, Nat.cast_zero, zero_add] at h
  simp only [zero_add] at heq
  rw [heq, hS] at h
  exact h

private theorem exp_le_rate (ε m c k s : ℝ) (hc : 0 < c) (hs : 0 < s) (hsk : s ≤ k + 1)
    (hm : 0 ≤ m) (hk : 0 ≤ k + 1) (hε : (k + 1) * m ≤ 2 * ε) :
    Real.exp (-2 * ε ^ 2 / (s * c)) ≤ Real.exp (-(m ^ 2 / (2 * c)) * (k + 1)) := by
  apply Real.exp_le_exp.2
  have h1 : 0 ≤ (k + 1) * m := mul_nonneg hk hm
  have h2 : ((k + 1) * m) ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ h1 hε 2
  have h3 : m ^ 2 * (k + 1) * s ≤ m ^ 2 * (k + 1) * (k + 1) :=
    mul_le_mul_of_nonneg_left hsk (by positivity)
  have e : -2 * ε ^ 2 / (s * c) = -(2 * ε ^ 2 / (s * c)) := by ring
  rw [e, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith

/-- Exponential form of the window bound: under honest majority (`0 < m`) and for windows long
enough that `4 t p ≤ (k - 3) m`, typicality fails on the window `[a, a + k]` with probability at
most `exp (-rate * (k + 1))`, `rate = m² / (2 (t + 1)²)`. -/
theorem BitcoinBackboneProb.window_bound_rate (n t : ℕ) (p : unitInterval) (a k : ℕ)
    (hk1 : 1 ≤ k) (hm : 0 < margin n t p) (hk : 4 * t * (p : ℝ) ≤ ((k : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤
      Real.exp (-rate n t p * ((k : ℝ) + 1)) := by
  have htp : 0 ≤ (t : ℝ) * p := mul_nonneg (Nat.cast_nonneg t) p.2.1
  have hk' : 2 * t * (p : ℝ) ≤ ((k : ℝ) - 1) * margin n t p := by nlinarith
  refine (window_bound n t p a k hk1 hk').trans ?_
  unfold rate
  exact exp_le_rate _ _ _ _ _ (by positivity) (by positivity) le_rfl hm.le (by positivity)
    (by nlinarith)

/-! ## Union bound over the windows of a horizon -/

/-- Union bound: if typicality fails on each window `[a, a + k]` with `lam ≤ k` with probability at
most `β`, then it fails somewhere on the horizon `[0, L]` with probability at most `L² β`. -/
theorem BitcoinBackboneProb.typicalOn_failure_le_of_window (n t : ℕ) (p : unitInterval)
    (lam L : ℕ) (hlam : 1 ≤ lam) (β : ℝ)
    (hβ : ∀ a k : ℕ, lam ≤ k → (P n t p).real
      {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤ β) :
    (P n t p).real {ω | ¬ TypicalOn ω lam L} ≤ (L : ℝ) ^ 2 * β := by
  classical
  have hβ0 : 0 ≤ β := measureReal_nonneg.trans (hβ 0 lam le_rfl)
  let W : Finset (ℕ × ℕ) := (Finset.range L ×ˢ Finset.Icc 1 L).filter (fun x => x.1 + lam ≤ x.2)
  let F : ℕ × ℕ → Set (Trace n t) := fun x =>
    {ω | ∑ i ∈ Finset.Ioo x.1 x.2, Y ω i ≤ ∑ i ∈ Finset.Icc x.1 x.2, Z ω i}
  have hsub : {ω : Trace n t | ¬ TypicalOn ω lam L} ⊆ ⋃ x ∈ W, F x := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, TypicalOn, not_forall, not_lt] at hω
    obtain ⟨a, b, hab, hbL, hfail⟩ := hω
    simp only [Set.mem_iUnion]
    refine ⟨(a, b), ?_, hfail⟩
    simp only [W, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    omega
  have hcard : (W.card : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : W.card ≤ L * L := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product]; simp
    have : (W.card : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; nlinarith
  calc (P n t p).real {ω | ¬ TypicalOn ω lam L}
      ≤ (P n t p).real (⋃ x ∈ W, F x) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ x ∈ W, (P n t p).real (F x) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ W, β := by
        apply Finset.sum_le_sum
        rintro ⟨a, b⟩ hx
        simp only [W, Finset.mem_filter] at hx
        obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
        exact hβ a k (by omega)
    _ = W.card * β := by simp
    _ ≤ (L : ℝ) ^ 2 * β := mul_le_mul_of_nonneg_right hcard hβ0

/-- Typicality on the horizon `[0, L]` fails with probability at most `L² exp (-rate (λ + 1))`
under honest majority (`0 < margin`) once `4 t p ≤ (λ - 3) margin`. -/
theorem BitcoinBackboneProb.typicalOn_failure_le (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 1 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ¬ TypicalOn ω lam L} ≤
      (L : ℝ) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by
  apply typicalOn_failure_le_of_window n t p lam L hlam
  intro a k hk'
  have hkl : (lam : ℝ) ≤ k := by exact_mod_cast hk'
  refine (window_bound_rate n t p a k (by omega) hm (by nlinarith)).trans ?_
  apply Real.exp_le_exp.2
  have : 0 ≤ rate n t p := by unfold rate; positivity
  nlinarith

/-- The same bound in "with high probability" form. -/
theorem BitcoinBackboneProb.typicalOn_prob_ge (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 1 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    1 - (L : ℝ) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) ≤
      (P n t p).real {ω | TypicalOn ω lam L} := by
  have h := typicalOn_failure_le n t p lam L hlam hm hk
  have hu : (P n t p).real Set.univ ≤
      (P n t p).real {ω | TypicalOn ω lam L} + (P n t p).real {ω | ¬ TypicalOn ω lam L} := by
    refine (measureReal_mono (fun ω _ => ?_)).trans (measureReal_union_le _ _)
    by_cases hω : TypicalOn ω lam L
    · exact Or.inl hω
    · exact Or.inr hω
  rw [probReal_univ] at hu
  linarith

/-! ## The induced execution and end-to-end composition -/

private theorem honestCount_toExecution {n t : ℕ} (ω : Trace n t) (L : ℕ)
    (base advParent : ℕ → ℕ → BitcoinBackbone.Chain) (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ L) :
    (toExecution ω L base advParent).honestCount r = honestCount (ω r) := by
  unfold BitcoinBackbone.Execution.honestCount honestCount
  rw [show (toExecution ω L base advParent).n = n from rfl, Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [toExecution, i.isLt, h1, h2]

private theorem Y_toExecution {n t : ℕ} (ω : Trace n t) (L : ℕ)
    (base advParent : ℕ → ℕ → BitcoinBackbone.Chain) (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ L) :
    (toExecution ω L base advParent).Y r = Y ω r := by
  unfold BitcoinBackbone.Execution.Y
  rw [honestCount_toExecution ω L base advParent r h1 h2]
  rfl

private theorem Y_toExecution_after {n t : ℕ} (ω : Trace n t) (L : ℕ)
    (base advParent : ℕ → ℕ → BitcoinBackbone.Chain) (r : ℕ) (hn : 0 < n) (h : L < r) :
    (toExecution ω L base advParent).Y r = 1 := by
  have hm : ∀ q, q ∈ Finset.range n →
      ((toExecution ω L base advParent).mined q r = true ↔ q = 0) := by
    intro q hq
    rw [Finset.mem_range] at hq
    simp only [toExecution, dif_pos hq]
    rw [if_neg (by omega)]
    simp [h]
  have hc : (toExecution ω L base advParent).honestCount r = 1 := by
    unfold BitcoinBackbone.Execution.honestCount
    rw [show (toExecution ω L base advParent).n = n from rfl, Finset.filter_congr hm,
      Finset.filter_eq' (Finset.range n) 0, if_pos (Finset.mem_range.2 hn)]
    rfl
  unfold BitcoinBackbone.Execution.Y
  rw [hc]; rfl

private theorem Z_toExecution {n t : ℕ} (ω : Trace n t) (L : ℕ)
    (base advParent : ℕ → ℕ → BitcoinBackbone.Chain) (r : ℕ) :
    (toExecution ω L base advParent).Z r = if r ≤ L then Z ω r else 0 := rfl

/-- The induced execution is typical for every network/adversary behaviour as soon as it is for
one: typicality only depends on the mining outcomes. -/
theorem BitcoinBackboneProb.typical_toExecution_iff {n t : ℕ} (ω : Trace n t) (lam L : ℕ)
    (base advParent : ℕ → ℕ → BitcoinBackbone.Chain) :
    (toExecution ω L base advParent).Typical lam ↔ TypicalTrunc ω lam L := by
  exact Iff.rfl

private theorem margin_pos_n_pos {n t : ℕ} {p : unitInterval} (hm : 0 < margin n t p) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    unfold margin at hm
    have : (0 : ℝ) ≤ t * p := mul_nonneg (Nat.cast_nonneg t) p.2.1
    simp at hm; linarith
  · exact h

private theorem expY_le_one (n t : ℕ) (p : unitInterval) :
    (n : ℝ) * p * (1 - (p : ℝ)) ^ (n - 1) ≤ 1 := by
  rw [← integral_roundY n t p]
  have : ∫ ρ, (roundY ρ : ℝ) ∂(roundMeasure n t p) ≤ ∫ _ρ, (1 : ℝ) ∂(roundMeasure n t p) :=
    integral_mono Integrable.of_finite (integrable_const _)
      (fun ρ => by have := roundY_le_one ρ; simp only; exact_mod_cast this)
  simpa using this

private theorem crossing_bound (n t : ℕ) (p : unitInterval) (lam L a : ℕ) (ha : a ≤ L)
    (hm : 0 < margin n t p) (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ∑ i ∈ Finset.Ioc a L, Y ω i + (a + lam - (L + 1)) ≤
      ∑ i ∈ Finset.Icc a L, Z ω i} ≤ Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by
  set j₀ := a + lam - (L + 1) with hj₀
  set d : ℝ := ((L - a : ℕ) : ℝ) with hd
  have hS : ((Finset.Icc a L).card : ℝ) = d + 1 := by
    rw [Nat.card_Icc, show L + 1 - a = (L - a) + 1 by omega]; push_cast; rfl
  have hT : ((Finset.Ioc a L).card : ℝ) = d := by rw [Nat.card_Ioc]
  set y : ℝ := n * p * (1 - (p : ℝ)) ^ (n - 1) with hy
  set z : ℝ := t * p with hz
  have hy1 : y ≤ 1 := expY_le_one n t p
  have hz0 : 0 ≤ z := mul_nonneg (Nat.cast_nonneg t) p.2.1
  have hmyz : margin n t p = y - z := rfl
  have hnat : lam ≤ (L - a) + j₀ + 1 := by omega
  have hreal : (lam : ℝ) ≤ d + j₀ + 1 := by
    have : ((lam : ℕ) : ℝ) ≤ (((L - a) + j₀ + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this; simpa [hd] using this
  have hj0 : (0 : ℝ) ≤ j₀ := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hkey : (d + j₀ + 1 + 1) * margin n t p ≤ 2 * ((j₀ : ℝ) + d * y - (d + 1) * z) := by
    have h1 : ((lam : ℝ) - 3) * margin n t p ≤ (d + j₀ - 2) * margin n t p :=
      mul_le_mul_of_nonneg_right (by linarith) hm.le
    rw [hmyz] at h1 ⊢
    nlinarith
  have hε : 0 ≤ (j₀ : ℝ) + ((Finset.Ioc a L).card : ℝ) * y - ((Finset.Icc a L).card : ℝ) * z := by
    rw [hS, hT]
    have : 0 ≤ (d + j₀ + 1 + 1) * margin n t p := by positivity
    linarith
  have h := sets_hoeffding n t p (Finset.Icc a L) (Finset.Ioc a L) Finset.Ioc_subset_Icc_self j₀ hε
  refine h.trans ?_
  rw [hS, hT]
  refine (exp_le_rate _ (margin n t p) _ (d + j₀ + 1) _ (by positivity) (by positivity)
    (by linarith) hm.le (by positivity) hkey).trans ?_
  apply Real.exp_le_exp.2
  have : 0 ≤ rate n t p := by unfold rate; positivity
  change -rate n t p * (d + j₀ + 1 + 1) ≤ -rate n t p * ((lam : ℝ) + 1)
  nlinarith

/-- Typicality of the induced execution (`BitcoinBackbone.Execution.Typical` for every window,
including the windows crossing or beyond the horizon `L`) fails with probability at most
`(L + 1)² exp (-rate (λ + 1))` under honest majority, for `λ ≥ 2` with `4 t p ≤ (λ - 3) margin`. -/
theorem BitcoinBackboneProb.typicalTrunc_failure_le (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 2 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ¬ TypicalTrunc ω lam L} ≤
      ((L : ℝ) + 1) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by
  classical
  have hn : 0 < n := margin_pos_n_pos hm
  let G : ℕ → Set (Trace n t) := fun a =>
    {ω | ∑ i ∈ Finset.Ioc a L, Y ω i + (a + lam - (L + 1)) ≤ ∑ i ∈ Finset.Icc a L, Z ω i}
  have hsub : {ω : Trace n t | ¬ TypicalTrunc ω lam L} ⊆
      {ω | ¬ TypicalOn ω lam L} ∪ ⋃ a ∈ Finset.range (L + 1), G a := by
    intro ω hω
    set E := toExecution ω L (fun _ _ => []) (fun _ _ => []) with hE
    have hω' : ¬ E.Typical lam := hω
    simp only [BitcoinBackbone.Execution.Typical, not_forall, not_lt] at hω'
    obtain ⟨a, b, hab, hfail⟩ := hω'
    have hZ : ∀ i, E.Z i = if i ≤ L then Z ω i else 0 := fun i => rfl
    by_cases hb : b ≤ L
    · left
      intro hT
      have h1 := hT a b hab hb
      have e1 : ∑ i ∈ Finset.Icc a b, E.Z i = ∑ i ∈ Finset.Icc a b, Z ω i := by
        apply Finset.sum_congr rfl
        intro i hi; rw [Finset.mem_Icc] at hi; rw [hZ, if_pos (by omega)]
      have e2 : ∑ i ∈ Finset.Ioo a b, E.Y i = ∑ i ∈ Finset.Ioo a b, Y ω i := by
        apply Finset.sum_congr rfl
        intro i hi; rw [Finset.mem_Ioo] at hi
        exact Y_toExecution ω L _ _ i (by omega) (by omega)
      rw [e1, e2] at hfail
      omega
    · have eZ : ∑ i ∈ Finset.Icc a b, E.Z i = ∑ i ∈ Finset.Icc a L, Z ω i := by
        simp only [hZ]
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [eZ] at hfail
      by_cases ha : a ≤ L
      · have eY : ∑ i ∈ Finset.Ioo a b, E.Y i =
            ∑ i ∈ Finset.Ioc a L, Y ω i + (b - (L + 1)) := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioo a b) (fun i => i ≤ L)]
          have f1 : (Finset.Ioo a b).filter (fun i => i ≤ L) = Finset.Ioc a L := by
            ext i; simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ioc]; omega
          have f2 : (Finset.Ioo a b).filter (fun i => ¬ i ≤ L) = Finset.Ioo L b := by
            ext i; simp only [Finset.mem_filter, Finset.mem_Ioo]; omega
          rw [f1, f2]
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi; rw [Finset.mem_Ioc] at hi
            exact Y_toExecution ω L _ _ i (by omega) (by omega)
          · rw [Finset.sum_congr rfl (fun i hi => Y_toExecution_after ω L _ _ i hn
              (Finset.mem_Ioo.1 hi).1)]
            simp only [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ioo]
            omega
        rw [eY] at hfail
        right
        simp only [Set.mem_iUnion]
        refine ⟨a, Finset.mem_range.2 (by omega), ?_⟩
        show ∑ i ∈ Finset.Ioc a L, Y ω i + (a + lam - (L + 1)) ≤ ∑ i ∈ Finset.Icc a L, Z ω i
        omega
      · exfalso
        have eY : ∑ i ∈ Finset.Ioo a b, E.Y i = b - a - 1 := by
          rw [Finset.sum_congr rfl (fun i hi => Y_toExecution_after ω L _ _ i hn
            (by have := (Finset.mem_Ioo.1 hi).1; omega))]
          simp
        have : Finset.Icc a L = ∅ := Finset.Icc_eq_empty (by omega)
        rw [this, eY] at hfail
        simp at hfail
        omega
  have hU := typicalOn_failure_le n t p lam L (by omega) hm hk
  set e := Real.exp (-rate n t p * ((lam : ℝ) + 1))
  have he : 0 ≤ e := (Real.exp_pos _).le
  calc (P n t p).real {ω | ¬ TypicalTrunc ω lam L}
      ≤ (P n t p).real ({ω | ¬ TypicalOn ω lam L} ∪ ⋃ a ∈ Finset.range (L + 1), G a) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (P n t p).real {ω | ¬ TypicalOn ω lam L} +
          (P n t p).real (⋃ a ∈ Finset.range (L + 1), G a) := measureReal_union_le _ _
    _ ≤ (L : ℝ) ^ 2 * e + ∑ _a ∈ Finset.range (L + 1), e := by
        gcongr
        refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum ?_)
        intro a ha
        exact crossing_bound n t p lam L a (by simpa [Nat.lt_succ_iff] using ha) hm hk
    _ ≤ ((L : ℝ) + 1) ^ 2 * e := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) L]

/-- End-to-end statement: for any property `Q` that the deterministic backbone analysis
guarantees for every legal typical execution (e.g. `BitcoinBackbone.common_prefix`,
`BitcoinBackbone.chain_quality`), the probability that some legal behaviour of the network and of
the adversary on the horizon `L` violates `Q` is at most `(L + 1)² exp (-rate (λ + 1))`. -/
theorem BitcoinBackboneProb.backbone_failure_le (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 2 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p)
    (Q : BitcoinBackbone.Execution → Prop)
    (hdet : ∀ E : BitcoinBackbone.Execution, E.Legal → E.Typical lam → Q E) :
    (P n t p).real {ω | ∃ base advParent : ℕ → ℕ → BitcoinBackbone.Chain,
      (toExecution ω L base advParent).Legal ∧ ¬ Q (toExecution ω L base advParent)} ≤
      ((L : ℝ) + 1) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (typicalTrunc_failure_le n t p lam L hlam hm hk)
  rintro ω ⟨base, advParent, hL, hQ⟩ hT
  exact hQ (hdet _ hL ((typical_toExecution_iff ω lam L base advParent).2 hT))

/-- End-to-end statement, "with high probability" form: with probability at least
`1 - (L + 1)² exp (-rate (λ + 1))`, every legal execution induced by the trace on the horizon `L`
satisfies `Q`. -/
theorem BitcoinBackboneProb.backbone_prob_ge (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 2 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p)
    (Q : BitcoinBackbone.Execution → Prop)
    (hdet : ∀ E : BitcoinBackbone.Execution, E.Legal → E.Typical lam → Q E) :
    1 - ((L : ℝ) + 1) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) ≤
      (P n t p).real {ω | ∀ base advParent : ℕ → ℕ → BitcoinBackbone.Chain,
        (toExecution ω L base advParent).Legal → Q (toExecution ω L base advParent)} := by
  have h := backbone_failure_le n t p lam L hlam hm hk Q hdet
  have hu : (P n t p).real Set.univ ≤
      (P n t p).real {ω | ∀ base advParent : ℕ → ℕ → BitcoinBackbone.Chain,
        (toExecution ω L base advParent).Legal → Q (toExecution ω L base advParent)} +
      (P n t p).real {ω | ∃ base advParent : ℕ → ℕ → BitcoinBackbone.Chain,
        (toExecution ω L base advParent).Legal ∧ ¬ Q (toExecution ω L base advParent)} := by
    refine (measureReal_mono (fun ω _ => ?_)).trans (measureReal_union_le _ _)
    by_cases hω : ∀ base advParent : ℕ → ℕ → BitcoinBackbone.Chain,
        (toExecution ω L base advParent).Legal → Q (toExecution ω L base advParent)
    · exact Or.inl hω
    · right
      push Not at hω
      exact hω
  rw [probReal_univ] at hu
  linarith
