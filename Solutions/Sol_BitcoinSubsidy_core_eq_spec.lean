import Definitions.Def_BitcoinSubsidy

open BitcoinSubsidy

theorem solution (height : Nat) : coreSubsidy height = specSubsidy height := by
  unfold coreSubsidy specSubsidy
  simp only []
  split
  · rename_i h
    symm
    apply Nat.div_eq_of_lt
    calc 50 * COIN < 2 ^ 64 := by decide
      _ ≤ 2 ^ (height / halvingInterval) := Nat.pow_le_pow_right (by decide) h
  · exact Nat.shiftRight_eq_div_pow _ _
