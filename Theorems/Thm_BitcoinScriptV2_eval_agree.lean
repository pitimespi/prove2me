import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.eval_agree (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (hl : BitcoinScriptV2.annotate script = some l)
    (hok : BitcoinScriptV2.RunOk f v o ⟨BitcoinScript.State.initial stack, script⟩ l) :
    BitcoinScriptV2.evalScriptV2 f v o stack script =
      BitcoinScript.evalScript f (BitcoinScriptV2.withCodeSig o v script) stack (l.map Prod.fst) := by sorry
