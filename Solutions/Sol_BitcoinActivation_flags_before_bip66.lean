import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- Before BIP66 a non-exception block enforces exactly the base flags. -/
theorem solution (height : Nat) (h : height < 363725) :
    BitcoinActivation.blockScriptFlags height .none = BitcoinActivation.baseFlags := by
  unfold blockScriptFlags exceptionBase baseFlags activeAt deploymentHeight
  simp only [Bool.false_or]
  have h1 : ¬ (363725 ≤ height) := by omega
  have h2 : ¬ (388381 ≤ height) := by omega
  have h3 : ¬ (419328 ≤ height) := by omega
  have h4 : ¬ (481824 ≤ height) := by omega
  simp [h1, h2, h3, h4]
