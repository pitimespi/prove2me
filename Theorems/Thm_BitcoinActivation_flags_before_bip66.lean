import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.flags_before_bip66 (height : Nat) (h : height < 363725) :
    BitcoinActivation.blockScriptFlags height .none = BitcoinActivation.baseFlags := by sorry
