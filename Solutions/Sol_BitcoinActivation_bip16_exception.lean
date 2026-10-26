import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- The BIP16 exception block (height 170060, before BIP66) enforces no script flags at all. -/
theorem solution (height : Nat) (h : height < 363725) :
    BitcoinActivation.blockScriptFlags height .bip16Block = BitcoinActivation.noFlags := by
  unfold blockScriptFlags exceptionBase noFlags activeAt deploymentHeight
  have h1 : ¬ (363725 ≤ height) := by omega
  have h2 : ¬ (388381 ≤ height) := by omega
  have h3 : ¬ (419328 ≤ height) := by omega
  have h4 : ¬ (481824 ≤ height) := by omega
  simp [h1, h2, h3, h4]
