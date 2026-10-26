import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- The Taproot exception block (height 692261, after SegWit) enforces every flag except Taproot. -/
theorem solution (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .taprootBlock = ⟨true, true, false, true, true, true, true⟩ := by
  unfold blockScriptFlags exceptionBase activeAt deploymentHeight
  have h1 : 363725 ≤ height := by omega
  have h2 : 388381 ≤ height := by omega
  have h3 : 419328 ≤ height := by omega
  simp [h, h1, h2, h3]
