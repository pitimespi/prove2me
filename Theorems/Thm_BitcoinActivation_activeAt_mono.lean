import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.activeAt_mono (dep : BuriedDeployment) (h₁ h₂ : Nat) (h : h₁ ≤ h₂)
    (ha : BitcoinActivation.activeAt h₁ dep = true) : BitcoinActivation.activeAt h₂ dep = true := by sorry
