import Definitions.Def_BitcoinSubsidy

theorem BitcoinSubsidy.subsidy_antitone (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    coreSubsidy h₂ ≤ coreSubsidy h₁ := by sorry
