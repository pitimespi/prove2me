import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.flags_mono (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags h₁ .none)
      (BitcoinActivation.blockScriptFlags h₂ .none) := by sorry
