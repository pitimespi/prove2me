import Definitions.Def_BitcoinSubsidy
import Theorems.Thm_BitcoinSubsidy_issuance_le_total

open BitcoinSubsidy

theorem solution (n : Nat) : issuedBelow n < MAX_MONEY := by
  calc issuedBelow n ≤ 2099999997690000 := BitcoinSubsidy.issuance_le_total n
    _ < MAX_MONEY := by decide
