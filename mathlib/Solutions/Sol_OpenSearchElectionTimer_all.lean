import Definitions.Def_OpenSearchElectionTimer

open OpenSearchPreVote OpenSearchElectionTimer

/-! # Randomized election timers -/

/-! Helper lemmas. `nonNegative ∘ toLong` maps each half of `Fin (2^64)` bijectively onto `[0, 2^63)`, which gives
the exact distribution of a delay. -/

/-- `nonNegative (toLong x)` in terms of `x.val`: the lower half of `Fin (2^64)` (the negative longs and
`Long.MIN_VALUE`) goes to `(2^63 - x) % 2^63`, the upper half (the non-negative longs) to `x - 2^63`. -/
private theorem nonNegative_toLong (x : Fin (2 ^ 64)) :
    nonNegative (toLong x) = if x.val < 2 ^ 63 then (2 ^ 63 - x.val) % 2 ^ 63 else x.val - 2 ^ 63 := by
  have hx := x.isLt
  unfold nonNegative toLong
  split_ifs <;> omega

/-- `nonNegative ∘ toLong` is exactly two-to-one from `Fin (2^64)` onto `[0, 2^63)`. -/
private theorem card_filter_nonNegative (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => P (nonNegative (toLong x)))).card =
      2 * ((Finset.range (2 ^ 63)).filter P).card := by
  rw [← Finset.card_filter_add_card_filter_not (p := fun x : Fin (2 ^ 64) => x.val < 2 ^ 63),
    Finset.filter_filter, Finset.filter_filter]
  have h1 : (Finset.univ.filter (fun x : Fin (2 ^ 64) =>
      P (nonNegative (toLong x)) ∧ x.val < 2 ^ 63)).card = ((Finset.range (2 ^ 63)).filter P).card := by
    apply Finset.card_nbij' (fun x => (2 ^ 63 - x.val) % 2 ^ 63)
      (fun w => ⟨(2 ^ 63 - w) % 2 ^ 63, by omega⟩)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hx ⊢
      rw [nonNegative_toLong, if_pos hx.2] at hx
      exact ⟨by omega, hx.1⟩
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hw ⊢
      have hlt : (2 ^ 63 - w) % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by norm_num)
      refine ⟨?_, hlt⟩
      rw [nonNegative_toLong, if_pos hlt]
      have : (2 ^ 63 - (2 ^ 63 - w) % 2 ^ 63) % 2 ^ 63 = w := by omega
      rw [this]; exact hw.2
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      ext; simp only; omega
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hw
      simp only; omega
  have h2 : (Finset.univ.filter (fun x : Fin (2 ^ 64) =>
      P (nonNegative (toLong x)) ∧ ¬ x.val < 2 ^ 63)).card = ((Finset.range (2 ^ 63)).filter P).card := by
    apply Finset.card_nbij' (fun x => x.val - 2 ^ 63)
      (fun w => ⟨(w % 2 ^ 63) + 2 ^ 63, by omega⟩)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hx ⊢
      rw [nonNegative_toLong, if_neg hx.2] at hx
      exact ⟨by omega, hx.1⟩
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hw ⊢
      have hlt : ¬ (w % 2 ^ 63) + 2 ^ 63 < 2 ^ 63 := by omega
      refine ⟨?_, hlt⟩
      rw [nonNegative_toLong, if_neg hlt]
      have : (w % 2 ^ 63) + 2 ^ 63 - 2 ^ 63 = w := by omega
      rw [this]; exact hw.2
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      ext; simp only; omega
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hw
      simp only; omega
  rw [h1, h2]; ring

/-- The `w < N` with `w % M = d - 1` are the `d - 1 + k M` for `k ≤ (N - d) / M`. -/
private theorem card_mod_eq (N M d : ℕ) (hM : 1 ≤ M) (hd : 1 ≤ d) (hdM : d ≤ M) (hMN : M ≤ N) :
    ((Finset.range N).filter (fun w => w % M + 1 = d)).card = (N - d) / M + 1 := by
  have key : (Finset.range N).filter (fun w => w % M + 1 = d) =
      (Finset.range ((N - d) / M + 1)).image (fun k => d - 1 + k * M) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hw, hwd⟩
      have h := Nat.div_add_mod w M
      have hc : M * (w / M) = w / M * M := Nat.mul_comm _ _
      refine ⟨w / M, ?_, ?_⟩
      · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega)]
        omega
      · omega
    · rintro ⟨k, hk, rfl⟩
      have hk' : k * M ≤ N - d := by
        have : k ≤ (N - d) / M := by omega
        calc k * M ≤ (N - d) / M * M := Nat.mul_le_mul_right _ this
          _ ≤ N - d := Nat.div_mul_le_self _ _
      constructor
      · omega
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]; omega
  rw [key, Finset.card_image_of_injective, Finset.card_range]
  intro k1 k2 h
  simp only at h
  have : k1 * M = k2 * M := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

/-- Every random delay lies between one millisecond and the bound. -/
theorem OpenSearchElectionTimer.randomDelay_range (M : Nat) (hM : 1 ≤ M) (x : Fin (2 ^ 64)) :
    1 ≤ randomDelay M x ∧ randomDelay M x ≤ M := by
  unfold randomDelay toPositiveLongAtMost
  have := Nat.mod_lt (nonNegative (toLong x)) (by omega : M > 0)
  omega

/-- **The exact distribution of a delay.** For a bound `1 ≤ M ≤ 2^63` and `1 ≤ d ≤ M`, exactly
`2 · (⌊(2^63 - d) / M⌋ + 1)` of the `2^64` values of `random.nextLong()` give the delay `d`. -/
theorem OpenSearchElectionTimer.randomDelay_card (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card = 2 * ((2 ^ 63 - d) / M + 1) := by
  unfold randomDelay toPositiveLongAtMost
  rw [card_filter_nonNegative (fun w => w % M + 1 = d), card_mod_eq _ _ _ hM hd hdM hM']

/-- **Delays are uniform up to a relative error of `M / 2^63`.** Each delay `d ∈ [1, M]` has between
`2 ⌊2^63 / M⌋` and `2 ⌈2^63 / M⌉` preimages among the `2^64` longs. -/
theorem OpenSearchElectionTimer.randomDelay_near_uniform (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    2 * (2 ^ 63 / M) ≤ (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card ∧
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card ≤ 2 * ((2 ^ 63 + M - 1) / M) := by
  rw [OpenSearchElectionTimer.randomDelay_card M d hM hM' hd hdM]
  have e : (2 ^ 63 - d) / M + 1 = (2 ^ 63 - d + M) / M := (Nat.add_div_right _ (by omega)).symm
  rw [e]
  constructor
  · exact Nat.mul_le_mul_left _ (Nat.div_le_div_right (by omega))
  · exact Nat.mul_le_mul_left _ (Nat.div_le_div_right (by omega))

/-- The ceiling `⌈N / b⌉ = (N + b - 1) / b` is antitone in `b ≥ 1`. -/
private theorem ceil_div_anti (N a b : ℕ) (hN : 1 ≤ N) (ha : 1 ≤ a) (hab : a ≤ b) :
    (N + b - 1) / b ≤ (N + a - 1) / a := by
  have h1 : N + b - 1 = (N - 1) + b := by omega
  have h2 : N + a - 1 = (N - 1) + a := by omega
  rw [h1, h2, Nat.add_div_right _ (by omega), Nat.add_div_right _ (by omega)]
  exact Nat.add_le_add_right (Nat.div_le_div_left hab (by omega)) 1

/-- For a fixed target `t`, few draws give a delay within `δ` of `t`. -/
private theorem card_close_le (t : ℤ) (Mb Mmin δ : ℕ) (hM : 1 ≤ Mmin)
    (hMb : Mmin ≤ Mb ∧ Mb ≤ 2 ^ 63) (hδ : 1 ≤ δ) :
    (Finset.univ.filter (fun y : Fin (2 ^ 64) => |t - (randomDelay Mb y : ℤ)| < δ)).card ≤
      (2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin)) := by
  have key := Finset.card_le_mul_card_image_of_maps_to
    (f := fun y : Fin (2 ^ 64) => (randomDelay Mb y : ℤ))
    (s := Finset.univ.filter (fun y : Fin (2 ^ 64) => |t - (randomDelay Mb y : ℤ)| < δ))
    (t := Finset.Ioo (t - δ) (t + δ)) ?_ (2 * ((2 ^ 63 + Mmin - 1) / Mmin)) ?_
  · rw [Int.card_Ioo] at key
    have e : (t + δ - (t - δ) - 1).toNat = 2 * δ - 1 := by omega
    rw [e] at key
    rw [Nat.mul_comm]; exact key
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_Ioo]
    rw [abs_lt] at hy
    constructor <;> linarith [hy.1, hy.2]
  · intro e _
    calc (Finset.filter (fun y => (randomDelay Mb y : ℤ) = e)
          (Finset.univ.filter (fun y : Fin (2 ^ 64) => |t - (randomDelay Mb y : ℤ)| < δ))).card
        ≤ (Finset.univ.filter (fun y : Fin (2 ^ 64) => (randomDelay Mb y : ℤ) = e)).card := by
          apply Finset.card_le_card
          intro y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun h => h.2
      _ ≤ 2 * ((2 ^ 63 + Mmin - 1) / Mmin) := by
          by_cases he : 1 ≤ e ∧ e ≤ Mb
          · obtain ⟨d, rfl⟩ : ∃ d : ℕ, e = d := ⟨e.toNat, by omega⟩
            simp only [Nat.cast_inj]
            have h1 := (OpenSearchElectionTimer.randomDelay_near_uniform Mb d (by omega) hMb.2
              (by omega) (by omega)).2
            exact h1.trans (Nat.mul_le_mul_left _ (ceil_div_anti _ _ _ (by norm_num) hM hMb.1))
          · have : Finset.univ.filter (fun y : Fin (2 ^ 64) => (randomDelay Mb y : ℤ) = e) = ∅ := by
              ext y
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false]
              intro h
              have := OpenSearchElectionTimer.randomDelay_range Mb (by omega) y
              omega
            rw [this, Finset.card_empty]
            exact Nat.zero_le _

/-- **Two timers fire less than `δ` apart with probability at most about `(2δ - 1) / Mmin`.** Whatever their offsets
and the first timer's bound, for a second bound between `Mmin ≥ 1` and `2^63`, the probability that the two candidates
fire less than `δ ≥ 1` apart is at most `(2δ - 1) · ⌈2^63 / Mmin⌉ / 2^63`. -/
theorem OpenSearchElectionTimer.close_pair_prob (a b : Int) (Ma Mb Mmin δ : Nat) (hM : 1 ≤ Mmin)
    (hMb : Mmin ≤ Mb ∧ Mb ≤ 2 ^ 63) (hδ : 1 ≤ δ) :
    ((Finset.univ.filter (fun p : Fin (2 ^ 64) × Fin (2 ^ 64) =>
        |(a + randomDelay Ma p.1) - (b + randomDelay Mb p.2)| < δ)).card : ℚ) / (2 ^ 64) ^ 2 ≤
      (2 * δ - 1 : ℕ) * ((2 ^ 63 + Mmin - 1) / Mmin : ℕ) / 2 ^ 63 := by
  -- The first draw is summed over freely: only the second bound matters.
  have hcount : (Finset.univ.filter (fun p : Fin (2 ^ 64) × Fin (2 ^ 64) =>
        |(a + randomDelay Ma p.1) - (b + randomDelay Mb p.2)| < δ)).card ≤
        2 ^ 64 * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin))) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    calc ∑ x : Fin (2 ^ 64), ∑ y : Fin (2 ^ 64),
          (if |(a + randomDelay Ma (x, y).1) - (b + randomDelay Mb (x, y).2)| < δ then 1 else 0)
        = ∑ x : Fin (2 ^ 64), (Finset.univ.filter (fun y : Fin (2 ^ 64) =>
            |(a + randomDelay Ma x - b) - (randomDelay Mb y : ℤ)| < δ)).card := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl
          intro y _
          have : (a + randomDelay Ma x) - (b + randomDelay Mb y) =
              (a + randomDelay Ma x - b) - (randomDelay Mb y : ℤ) := by ring
          simp only [this]
      _ ≤ ∑ _x : Fin (2 ^ 64), (2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin)) :=
          Finset.sum_le_sum (fun x _ => card_close_le _ Mb Mmin δ hM hMb hδ)
      _ = 2 ^ 64 * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hq : ((Finset.univ.filter (fun p : Fin (2 ^ 64) × Fin (2 ^ 64) =>
        |(a + randomDelay Ma p.1) - (b + randomDelay Mb p.2)| < δ)).card : ℚ) ≤
        2 ^ 64 * (((2 * δ - 1 : ℕ) : ℚ) * (2 * (((2 ^ 63 + Mmin - 1) / Mmin : ℕ) : ℚ))) := by
    exact_mod_cast hcount
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc _ ≤ 2 ^ 64 * (((2 * δ - 1 : ℕ) : ℚ) * (2 * (((2 ^ 63 + Mmin - 1) / Mmin : ℕ) : ℚ))) * 2 ^ 63 :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring

/-- Sum over `ι → A` by splitting off the coordinate `j`. -/
private theorem sum_piSplitAt {ι A M : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [AddCommMonoid M] (j : ι) (F : (ι → A) → M) :
    ∑ x, F x = ∑ r : {k // k ≠ j} → A, ∑ y : A, F ((Equiv.piSplitAt j (fun _ => A)).symm (y, r)) := by
  rw [← (Equiv.piSplitAt j (fun _ => A)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]

/-- The coordinate split off by `Equiv.piSplitAt`. -/
private theorem piSplitAt_symm_self {ι A : Type*} [DecidableEq ι] (j : ι) (y : A)
    (r : {k // k ≠ j} → A) : (Equiv.piSplitAt j (fun _ => A)).symm (y, r) j = y := by
  simp [Equiv.piSplitAt_symm_apply]

/-- The other coordinates. -/
private theorem piSplitAt_symm_ne {ι A : Type*} [DecidableEq ι] (j : ι) (y : A)
    (r : {k // k ≠ j} → A) (k : ι) (hk : k ≠ j) :
    (Equiv.piSplitAt j (fun _ => A)).symm (y, r) k = r ⟨k, hk⟩ := by
  simp [Equiv.piSplitAt_symm_apply, hk]

/-- There are `C(n, 2)` pairs `i < j` in `Fin n`. -/
private theorem card_pairs_lt (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2)).card = n.choose 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ j : Fin n, (∑ i : Fin n, if (i, j).1 < (i, j).2 then 1 else 0) = j.val := by
    intro j
    rw [← Finset.card_filter, ← Fin.card_Iio j]
    congr 1
    ext i
    simp
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun m => m) n, Nat.choose_two_right, ← Finset.sum_range_id_mul_two,
    Nat.mul_div_cancel _ (by norm_num)]

/-- For two distinct candidates, few full draws make them fire less than `δ` apart. -/
private theorem card_pair_close_le (n δ Mmin : ℕ) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin n → Int) (bound : Fin n → Nat) (hbound : ∀ i, Mmin ≤ bound i ∧ bound i ≤ 2 ^ 63)
    (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ.filter (fun x : Fin n → Fin (2 ^ 64) =>
        |fireTime offset bound x i - fireTime offset bound x j| < δ)).card ≤
      (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin))) := by
  rw [Finset.card_filter, sum_piSplitAt j]
  calc ∑ r : {k // k ≠ j} → Fin (2 ^ 64), ∑ y : Fin (2 ^ 64),
        (if |fireTime offset bound ((Equiv.piSplitAt j (fun _ => Fin (2 ^ 64))).symm (y, r)) i -
            fireTime offset bound ((Equiv.piSplitAt j (fun _ => Fin (2 ^ 64))).symm (y, r)) j| < δ
          then 1 else 0)
      = ∑ r : {k // k ≠ j} → Fin (2 ^ 64), (Finset.univ.filter (fun y : Fin (2 ^ 64) =>
          |(offset i + randomDelay (bound i) (r ⟨i, hij⟩) - offset j) -
            (randomDelay (bound j) y : ℤ)| < δ)).card := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro y _
        unfold fireTime
        rw [piSplitAt_symm_self, piSplitAt_symm_ne _ _ _ _ hij]
        have : offset i + (randomDelay (bound i) (r ⟨i, hij⟩) : ℤ) -
            (offset j + (randomDelay (bound j) y : ℤ)) =
            (offset i + randomDelay (bound i) (r ⟨i, hij⟩) - offset j) -
              (randomDelay (bound j) y : ℤ) := by ring
        rw [this]
    _ ≤ ∑ _r : {k // k ≠ j} → Fin (2 ^ 64),
          (2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin)) :=
        Finset.sum_le_sum (fun r _ => card_close_le _ (bound j) Mmin δ hM (hbound j) hδ)
    _ = (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin))) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        congr 1
        simp

/-- **A round of competing timers is contested with probability at most `contestedBound n δ Mmin`.** For `n ≥ 1`
candidates with arbitrary offsets and with bounds between `Mmin ≥ 1` and `2^63`, the probability that no candidate fires
at least `δ ≥ 1` before all others is at most `contestedBound n δ Mmin = C(n,2) · (2δ - 1) · ⌈2^63 / Mmin⌉ / 2^63`,
which is small only when `Mmin` is much larger than `C(n,2) · (2δ - 1)`. -/
theorem OpenSearchElectionTimer.contested_prob_le (n δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin n → Int) (bound : Fin n → Nat) (hbound : ∀ i, Mmin ≤ bound i ∧ bound i ≤ 2 ^ 63) :
    ((Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card : ℚ) / (2 ^ 64) ^ n ≤
      contestedBound n δ Mmin := by
  set P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2) with hPdef
  set E : Fin n × Fin n → Finset (Fin n → Fin (2 ^ 64)) := fun ij =>
    Finset.univ.filter (fun x => |fireTime offset bound x ij.1 - fireTime offset bound x ij.2| < δ)
    with hEdef
  have hsub : Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x) ⊆ P.biUnion E := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fireTime offset bound x)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    unfold Uncontested at hx
    push Not at hx
    obtain ⟨j, hj, hlt⟩ := hx i0
    have hle := hi0 j (Finset.mem_univ _)
    simp only [Finset.mem_biUnion, hPdef, hEdef, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_or_gt_of_ne hj with h | h
    · exact ⟨(j, i0), h, by rw [abs_lt]; constructor <;> linarith⟩
    · exact ⟨(i0, j), h, by rw [abs_lt]; constructor <;> linarith⟩
  have hcount : (Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card ≤
      n.choose 2 * ((2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin)))) := by
    calc _ ≤ (P.biUnion E).card := Finset.card_le_card hsub
      _ ≤ ∑ ij ∈ P, (E ij).card := Finset.card_biUnion_le
      _ ≤ ∑ _ij ∈ P, (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin))) := by
          apply Finset.sum_le_sum
          intro ij hij
          simp only [hPdef, Finset.mem_filter, Finset.mem_univ, true_and] at hij
          exact card_pair_close_le n δ Mmin hδ hM offset bound hbound ij.1 ij.2 (ne_of_lt hij)
      _ = _ := by rw [Finset.sum_const, hPdef, card_pairs_lt, smul_eq_mul]
  have hq : ((Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card : ℚ) ≤
      (n.choose 2 : ℚ) * (((2 : ℚ) ^ 64) ^ (n - 1) * (((2 * δ - 1 : ℕ) : ℚ) *
        (2 * (((2 ^ 63 + Mmin - 1) / Mmin : ℕ) : ℚ)))) := by
    exact_mod_cast hcount
  have hpow : ((2 : ℚ) ^ 64) ^ n = ((2 : ℚ) ^ 64) ^ (n - 1) * 2 ^ 64 := by
    rw [← pow_succ]; congr 1; omega
  unfold contestedBound
  rw [div_le_div_iff₀ (by positivity) (by positivity), hpow]
  calc _ ≤ (n.choose 2 : ℚ) * (((2 : ℚ) ^ 64) ^ (n - 1) * (((2 * δ - 1 : ℕ) : ℚ) *
        (2 * (((2 ^ 63 + Mmin - 1) / Mmin : ℕ) : ℚ)))) * 2 ^ 63 :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring

/-- **Repeated contests become exponentially unlikely once the per-round bound is below 1, even against an adaptive
scheduler.** Over `K` rounds of the same `n ≥ 1` candidates, each drawing afresh in every round, let the offsets and
bounds of round `k` be any deterministic function of the draws of the earlier rounds (an adversary scheduling the
network may react to the draws of the earlier rounds, but not to those of round `k` or later ones), with every bound
between `Mmin ≥ 1` and `2^63`. The probability that all `K` rounds are contested with margin `δ ≥ 1` is at most
`contestedBound n δ Mmin ^ K`. -/
theorem OpenSearchElectionTimer.all_contested_prob_le (n K δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Int)
    (bound : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Nat)
    (hbound : ∀ k X i, Mmin ≤ bound k X i ∧ bound k X i ≤ 2 ^ 63)
    (hcausal : ∀ k X X', (∀ m : Fin K, m < k → X m = X' m) → offset k X = offset k X' ∧ bound k X = bound k X') :
    ((Finset.univ.filter (fun X : Fin K → Fin n → Fin (2 ^ 64) =>
        ∀ k, ¬ Uncontested (offset k X) (bound k X) δ (X k))).card : ℚ) / (2 ^ 64) ^ (n * K) ≤
      contestedBound n δ Mmin ^ K := by
  classical
  have hc0 : 0 ≤ contestedBound n δ Mmin := by unfold contestedBound; positivity
  -- `Pj j X`: the rounds before `j` are all contested
  let Pj : ℕ → (Fin K → Fin n → Fin (2 ^ 64)) → Prop := fun j X =>
    ∀ k : Fin K, k.val < j → ¬ Uncontested (offset k X) (bound k X) δ (X k)
  have hPj_congr : ∀ j X X', (∀ m : Fin K, m.val < j → X m = X' m) → (Pj j X ↔ Pj j X') := by
    intro j X X' h
    simp only [Pj]
    apply forall_congr'; intro k
    apply imp_congr_right; intro hk
    obtain ⟨ho, hb⟩ := hcausal k X X' (fun m hm => h m (by have := Fin.lt_def.mp hm; omega))
    rw [ho, hb, h k hk]
  let S : ℕ → ℚ := fun j => ∑ X : Fin K → Fin n → Fin (2 ^ 64), if Pj j X then (1 : ℚ) else 0
  have hS0 : S 0 = ((2 : ℚ) ^ 64) ^ (n * K) := by
    have : ∀ X, Pj 0 X := fun X k hk => absurd hk (Nat.not_lt_zero _)
    simp only [S, this, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [pow_mul]
    norm_num
  have hstep : ∀ j (hj : j < K), S (j + 1) ≤ contestedBound n δ Mmin * S j := by
    intro j hj
    obtain ⟨jj, hjj⟩ : ∃ jj : Fin K, jj.val = j := ⟨⟨j, hj⟩, rfl⟩
    have hsplit : ∀ X, Pj (j + 1) X ↔
        Pj j X ∧ ¬ Uncontested (offset jj X) (bound jj X) δ (X jj) := by
      intro X
      simp only [Pj]
      constructor
      · intro h
        exact ⟨fun k hk => h k (by omega), h jj (by omega)⟩
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · exact h1 k hk
        · have : k = jj := Fin.ext (by omega)
          rw [this]; exact h2
    simp only [S]
    rw [sum_piSplitAt jj, sum_piSplitAt jj, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have hagree : ∀ (y : Fin n → Fin (2 ^ 64)) (m : Fin K), m ≠ jj →
        (Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (y, r) m =
          (Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (fun _ => 0, r) m := by
      intro y m hm
      rw [piSplitAt_symm_ne _ _ _ _ hm, piSplitAt_symm_ne _ _ _ _ hm]
    have hP : ∀ y, Pj j ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (y, r)) ↔
        Pj j ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (fun _ => 0, r)) :=
      fun y => hPj_congr j _ _ (fun m hm => hagree y m (fun h => by rw [h] at hm; omega))
    have hOB : ∀ y,
        offset jj ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (y, r)) =
          offset jj ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (fun _ => 0, r)) ∧
        bound jj ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (y, r)) =
          bound jj ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (fun _ => 0, r)) :=
      fun y => hcausal jj _ _ (fun m hm => hagree y m (ne_of_lt hm))
    set X0 := (Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (fun _ => 0, r) with hX0
    have lhs : ∑ y : Fin n → Fin (2 ^ 64),
        (if Pj (j + 1) ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (y, r))
          then (1 : ℚ) else 0) =
        (if Pj j X0 then (1 : ℚ) else 0) *
          ((Finset.univ.filter (fun y => ¬ Uncontested (offset jj X0) (bound jj X0) δ y)).card : ℚ) := by
      rw [Finset.natCast_card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      have e1 : Pj (j + 1) ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (y, r)) ↔
          Pj j X0 ∧ ¬ Uncontested (offset jj X0) (bound jj X0) δ y := by
        rw [hsplit, hP y, (hOB y).1, (hOB y).2, piSplitAt_symm_self]
      by_cases h1 : Pj j X0
      · by_cases h2 : Uncontested (offset jj X0) (bound jj X0) δ y
        · rw [if_neg (fun h => (e1.mp h).2 h2), if_pos h1, if_neg (not_not.mpr h2), mul_zero]
        · rw [if_pos (e1.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2, mul_one]
      · rw [if_neg (fun h => h1 (e1.mp h).1), if_neg h1, zero_mul]
    have rhs : ∑ y : Fin n → Fin (2 ^ 64),
        (if Pj j ((Equiv.piSplitAt jj (fun _ => Fin n → Fin (2 ^ 64))).symm (y, r))
          then (1 : ℚ) else 0) = ((2 : ℚ) ^ 64) ^ n * (if Pj j X0 then (1 : ℚ) else 0) := by
      simp only [hP]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin]
      push_cast; ring
    rw [lhs, rhs]
    have hcp := OpenSearchElectionTimer.contested_prob_le n δ Mmin hn hδ hM (offset jj X0)
      (bound jj X0) (hbound jj X0)
    rw [div_le_iff₀ (by positivity)] at hcp
    have hind : (0 : ℚ) ≤ if Pj j X0 then (1 : ℚ) else 0 := by split_ifs <;> norm_num
    calc (if Pj j X0 then (1 : ℚ) else 0) *
          ((Finset.univ.filter (fun y => ¬ Uncontested (offset jj X0) (bound jj X0) δ y)).card : ℚ)
        ≤ (if Pj j X0 then (1 : ℚ) else 0) * (contestedBound n δ Mmin * ((2 : ℚ) ^ 64) ^ n) :=
          mul_le_mul_of_nonneg_left hcp hind
      _ = contestedBound n δ Mmin * (((2 : ℚ) ^ 64) ^ n * (if Pj j X0 then (1 : ℚ) else 0)) := by ring
  have hSK : ∀ j, j ≤ K → S j ≤ contestedBound n δ Mmin ^ j * ((2 : ℚ) ^ 64) ^ (n * K) := by
    intro j
    induction j with
    | zero => intro _; rw [hS0]; simp
    | succ j ih =>
      intro hj
      calc S (j + 1) ≤ contestedBound n δ Mmin * S j := hstep j (by omega)
        _ ≤ contestedBound n δ Mmin * (contestedBound n δ Mmin ^ j * ((2 : ℚ) ^ 64) ^ (n * K)) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hc0
        _ = contestedBound n δ Mmin ^ (j + 1) * ((2 : ℚ) ^ 64) ^ (n * K) := by ring
  have hfinal := hSK K le_rfl
  have hSK_eq : ((Finset.univ.filter (fun X : Fin K → Fin n → Fin (2 ^ 64) =>
        ∀ k, ¬ Uncontested (offset k X) (bound k X) δ (X k))).card : ℚ) = S K := by
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro X _
    have : (∀ k, ¬ Uncontested (offset k X) (bound k X) δ (X k)) ↔ Pj K X := by
      simp only [Pj]
      exact ⟨fun h k _ => h k, fun h k => h k k.isLt⟩
    by_cases h : Pj K X
    · rw [if_pos (this.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]
  rw [div_le_iff₀ (by positivity), hSK_eq]
  exact hfinal

/-- `contestedBound 3 100 10000`, the bound for three competing candidates, a margin of 100 ms (an illustrative choice:
nothing here shows that it suffices for a pre-voting round and an election) and every bound at least OpenSearch's
default `cluster.election.max_timeout` of 10 seconds (`Mmin = 10000`; with the default settings, every attempt from
attempt 99 on), is below 6%, and its fifth power is below one in a million. By `contested_prob_le` and
`all_contested_prob_le` these bound the probability that a round is contested and that five rounds are all contested.
The theorem itself is arithmetic on these literals. -/
theorem OpenSearchElectionTimer.default_example :
    contestedBound 3 100 10000 < 6 / 100 ∧ contestedBound 3 100 10000 ^ 5 < 1 / 1000000 := by
  unfold contestedBound
  norm_num [Nat.choose]
