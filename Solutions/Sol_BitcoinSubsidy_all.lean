import Definitions.Def_BitcoinSubsidy

open BitcoinSubsidy

-- Local development file: all six statements with proofs, to be split per theorem for submission.

theorem BitcoinSubsidy.core_eq_spec (height : Nat) : coreSubsidy height = specSubsidy height := by
  unfold coreSubsidy specSubsidy
  simp only []
  split
  · rename_i h
    symm
    apply Nat.div_eq_of_lt
    calc 50 * COIN < 2 ^ 64 := by decide
      _ ≤ 2 ^ (height / halvingInterval) := Nat.pow_le_pow_right (by decide) h
  · exact Nat.shiftRight_eq_div_pow _ _

theorem BitcoinSubsidy.subsidy_le_maxMoney (height : Nat) : coreSubsidy height ≤ MAX_MONEY := by
  rw [BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  calc (50 * COIN) / 2 ^ (height / halvingInterval) ≤ 50 * COIN := Nat.div_le_self _ _
    _ ≤ MAX_MONEY := by decide

theorem BitcoinSubsidy.subsidy_antitone (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    coreSubsidy h₂ ≤ coreSubsidy h₁ := by
  rw [BitcoinSubsidy.core_eq_spec, BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  apply Nat.div_le_div_left
  · exact Nat.pow_le_pow_right (by decide) (Nat.div_le_div_right h)
  · exact Nat.two_pow_pos _

theorem BitcoinSubsidy.subsidy_halving (height : Nat) :
    coreSubsidy (height + halvingInterval) = coreSubsidy height / 2 := by
  rw [BitcoinSubsidy.core_eq_spec, BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  rw [Nat.add_div_right _ (by decide : 0 < halvingInterval), Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem BitcoinSubsidy.subsidy_zero_iff (height : Nat) :
    coreSubsidy height = 0 ↔ zeroHeight ≤ height := by
  rw [BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy zeroHeight
  rw [Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  constructor
  · intro h
    have h33 : 33 ≤ height / halvingInterval := by
      rcases Nat.lt_or_ge (height / halvingInterval) 33 with hlt | hge
      · have hle : height / halvingInterval ≤ 32 := Nat.le_of_lt_succ hlt
        have h1 : 2 ^ (height / halvingInterval) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hle
        have h2 : (50 * COIN) < 2 ^ 32 := Nat.lt_of_lt_of_le h h1
        exact absurd h2 (by decide)
      · exact hge
    exact (Nat.le_div_iff_mul_le (by decide : 0 < halvingInterval)).1 h33
  · intro h
    have h33 : 33 ≤ height / halvingInterval :=
      (Nat.le_div_iff_mul_le (by decide : 0 < halvingInterval)).2 h
    calc 50 * COIN < 2 ^ 33 := by decide
      _ ≤ 2 ^ (height / halvingInterval) := Nat.pow_le_pow_right (by decide) h33

/-- Within one interval the subsidy is constant. -/
private theorem subsidy_in_interval (m j : Nat) (hj : j < halvingInterval) :
    coreSubsidy (halvingInterval * m + j) = (50 * COIN) / 2 ^ m := by
  rw [BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  have : (halvingInterval * m + j) / halvingInterval = m := by
    rw [Nat.mul_add_div (by decide : 0 < halvingInterval), Nat.div_eq_of_lt hj, Nat.add_zero]
  rw [this]

private theorem issued_partial (m j : Nat) (hj : j ≤ halvingInterval) :
    issuedBelow (halvingInterval * m + j) = issuedBelow (halvingInterval * m) + j * ((50 * COIN) / 2 ^ m) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, issuedBelow, ih (Nat.le_of_succ_le hj),
      subsidy_in_interval m j (Nat.lt_of_succ_le hj), Nat.add_mul, Nat.one_mul, Nat.add_assoc]

private theorem issued_intervals (m : Nat) :
    issuedBelow (halvingInterval * m) = halvingInterval * intervalSum m := by
  induction m with
  | zero => simp [issuedBelow, intervalSum]
  | succ m ih =>
    rw [Nat.mul_succ, issued_partial m halvingInterval (Nat.le_refl _), ih, intervalSum, Nat.mul_add]

private theorem issued_mono (a b : Nat) (h : a ≤ b) : issuedBelow a ≤ issuedBelow b := by
  induction b with
  | zero => cases Nat.le_zero.1 h; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.le_succ_iff.1 h with h' | h'
    · exact Nat.le_trans (ih h') (Nat.le_add_right _ _)
    · subst h'; exact Nat.le_refl _

private theorem issued_stable (n : Nat) (h : zeroHeight ≤ n) : issuedBelow n = issuedBelow zeroHeight := by
  induction n with
  | zero => cases Nat.le_zero.1 h
  | succ n ih =>
    rcases Nat.le_succ_iff.1 h with h' | h'
    · rw [issuedBelow, ih h', (BitcoinSubsidy.subsidy_zero_iff n).2 h', Nat.add_zero]
    · rw [h']

theorem BitcoinSubsidy.issuance_total : issuedBelow zeroHeight = 2099999997690000 := by
  have h := issued_intervals 33
  have hz : zeroHeight = halvingInterval * 33 := by decide
  rw [hz, h]
  decide

theorem BitcoinSubsidy.issuance_le_total (n : Nat) : issuedBelow n ≤ 2099999997690000 := by
  rw [← BitcoinSubsidy.issuance_total]
  by_cases h : zeroHeight ≤ n
  · rw [issued_stable n h]; exact Nat.le_refl _
  · exact issued_mono n zeroHeight (Nat.le_of_not_le h)

theorem BitcoinSubsidy.issuance_bound (n : Nat) : issuedBelow n < MAX_MONEY := by
  calc issuedBelow n ≤ 2099999997690000 := BitcoinSubsidy.issuance_le_total n
    _ < MAX_MONEY := by decide
