import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.stepV2_agree (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (sc : BitcoinScript.Bytes) (hsc : s.scriptCode = sc)
    (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes) (hok : BitcoinScriptV2.StepOk v s i) :
    BitcoinScriptV2.stepV2 f v o s (i, r) =
      (BitcoinScript.step f (BitcoinScriptV2.withCodeSig o v sc) s.st i).map fun st => ⟨st, sc⟩ := by sorry
