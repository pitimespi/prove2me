import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- From SegWit activation on, a non-exception block enforces every flag. -/
theorem solution (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .none = ⟨true, true, true, true, true, true, true⟩ := by
  unfold blockScriptFlags exceptionBase baseFlags activeAt deploymentHeight
  have h1 : 363725 ≤ height := by omega
  have h2 : 388381 ≤ height := by omega
  have h3 : 419328 ≤ height := by omega
  simp [h, h1, h2, h3]
