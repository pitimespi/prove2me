import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.bip16_exception (height : Nat) (h : height < 363725) :
    BitcoinActivation.blockScriptFlags height .bip16Block = BitcoinActivation.noFlags := by sorry
