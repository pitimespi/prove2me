import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.run_eq_runSeq (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle)
    (s : BitcoinScript.State) (sc : BitcoinScript.Script) :
    BitcoinScript.run f o s sc =
      match BitcoinMiniscript.runSeq f o s sc with
      | none => none
      | some s' => if s'.vfExec.isEmpty then some s' else none := by sorry
