import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.subsidy_zero_iff (height : Nat) :
    coreSubsidy height = 0 ↔ zeroHeight ≤ height := by sorry
