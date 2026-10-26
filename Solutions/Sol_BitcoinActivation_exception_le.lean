import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- An exception never enforces a flag the default would not: exceptions only remove rules. -/
theorem solution (height : Nat) (exc : ScriptException) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags height exc)
      (BitcoinActivation.blockScriptFlags height .none) := by
  cases exc <;>
  · unfold blockScriptFlags exceptionBase baseFlags noFlags ScriptFlags.le
    simp
