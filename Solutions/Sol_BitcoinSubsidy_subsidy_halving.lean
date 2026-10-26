import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSubsidy

theorem solution (height : Nat) :
    coreSubsidy (height + halvingInterval) = coreSubsidy height / 2 := by
  rw [BitcoinSubsidy.core_eq_spec, BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  rw [Nat.add_div_right _ (by decide : 0 < halvingInterval), Nat.pow_succ, Nat.div_div_eq_div_mul]
