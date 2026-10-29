import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.evalScript_eq_runSeq (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle)
    (st : List BitcoinScript.Bytes) (sc : BitcoinScript.Script) :
    BitcoinScript.evalScript f o st sc =
      match BitcoinMiniscript.runSeq f o (BitcoinScript.State.initial st) sc with
      | none => none
      | some s' => if s'.vfExec.isEmpty then some s'.stack else none := by sorry
