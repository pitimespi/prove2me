import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.exception_le (height : Nat) (exc : ScriptException) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags height exc)
      (BitcoinActivation.blockScriptFlags height .none) := by sorry
