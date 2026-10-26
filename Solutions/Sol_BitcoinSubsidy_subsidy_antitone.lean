import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSubsidy

theorem solution (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    coreSubsidy h₂ ≤ coreSubsidy h₁ := by
  rw [BitcoinSubsidy.core_eq_spec, BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  apply Nat.div_le_div_left
  · exact Nat.pow_le_pow_right (by decide) (Nat.div_le_div_right h)
  · exact Nat.two_pow_pos _
