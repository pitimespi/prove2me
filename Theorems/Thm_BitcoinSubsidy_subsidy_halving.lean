import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.subsidy_halving (height : Nat) :
    coreSubsidy (height + halvingInterval) = coreSubsidy height / 2 := by sorry
