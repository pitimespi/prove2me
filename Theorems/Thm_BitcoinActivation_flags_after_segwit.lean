import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.flags_after_segwit (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .none = ⟨true, true, true, true, true, true, true⟩ := by sorry
