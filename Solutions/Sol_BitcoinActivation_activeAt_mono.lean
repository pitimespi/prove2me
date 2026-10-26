import Definitions.Def_BitcoinActivation

open BitcoinActivation

theorem solution (dep : BuriedDeployment) (h₁ h₂ : Nat) (h : h₁ ≤ h₂)
    (ha : BitcoinActivation.activeAt h₁ dep = true) : BitcoinActivation.activeAt h₂ dep = true := by
  unfold activeAt at *
  simp only [decide_eq_true_eq] at *
  omega
