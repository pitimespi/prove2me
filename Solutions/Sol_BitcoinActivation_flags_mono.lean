import Definitions.Def_BitcoinActivation
import Theorems.Thm_BitcoinActivation_activeAt_mono

open BitcoinActivation

/-- Soft forks only add script rules: the flag set of a non-exception block is monotone in height. -/
theorem solution (h₁ h₂ : Nat) (h : h₁ ≤ h₂) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags h₁ .none)
      (BitcoinActivation.blockScriptFlags h₂ .none) := by
  unfold blockScriptFlags exceptionBase baseFlags ScriptFlags.le
  simp only [Bool.false_or]
  refine ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, ?_, ?_, ?_, ?_⟩ <;>
    exact BitcoinActivation.activeAt_mono _ h₁ h₂ h
