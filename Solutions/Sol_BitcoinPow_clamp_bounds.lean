import Definitions.Def_BitcoinPow

open BitcoinPow

theorem solution (actual : Int) :
    ((BitcoinPow.targetTimespan / 4 : Nat) : Int) ≤ BitcoinPow.clampTimespan actual ∧
    BitcoinPow.clampTimespan actual ≤ ((BitcoinPow.targetTimespan * 4 : Nat) : Int) := by
  unfold clampTimespan targetTimespan
  simp only []
  by_cases h1 : actual < ((14 * 24 * 60 * 60 / 4 : Nat) : Int)
  · rw [if_pos h1]; constructor <;> omega
  · rw [if_neg h1]
    by_cases h2 : ((14 * 24 * 60 * 60 * 4 : Nat) : Int) < actual
    · rw [if_pos h2]; constructor <;> omega
    · rw [if_neg h2]; constructor <;> omega
