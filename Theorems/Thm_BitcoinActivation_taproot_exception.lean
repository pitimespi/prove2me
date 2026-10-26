import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.taproot_exception (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .taprootBlock = ⟨true, true, false, true, true, true, true⟩ := by sorry
