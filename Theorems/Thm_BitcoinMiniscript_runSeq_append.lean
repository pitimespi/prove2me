import Definitions.Def_BitcoinMiniscript
import Definitions.Def_BitcoinScript
open BitcoinMiniscript BitcoinToLocal BitcoinHtlc BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinMiniscript.runSeq_append (f : BitcoinScript.Flags) (o : BitcoinScript.Oracle)
    (s : BitcoinScript.State) (a b : BitcoinScript.Script) :
    BitcoinMiniscript.runSeq f o s (a ++ b) =
      match BitcoinMiniscript.runSeq f o s a with
      | none => none
      | some s' => BitcoinMiniscript.runSeq f o s' b := by sorry
