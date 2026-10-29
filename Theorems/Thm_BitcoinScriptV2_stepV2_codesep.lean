import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.stepV2_codesep (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s s' : BitcoinScriptV2.StateV2) (r : BitcoinScript.Bytes) (hexec : BitcoinScript.allTrue s.st.vfExec = true)
    (h : BitcoinScriptV2.stepV2 f v o s (.op BitcoinScript.OP_CODESEPARATOR, r) = some s') :
    s'.scriptCode = r := by sorry
