import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_core_eq_spec

open BitcoinSubsidy

theorem solution (height : Nat) : coreSubsidy height ≤ MAX_MONEY := by
  rw [BitcoinSubsidy.core_eq_spec]
  unfold specSubsidy
  calc (50 * COIN) / 2 ^ (height / halvingInterval) ≤ 50 * COIN := Nat.div_le_self _ _
    _ ≤ MAX_MONEY := by decide
