import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.stepV2_keeps (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s s' : BitcoinScriptV2.StateV2) (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes)
    (hno : i ≠ .op BitcoinScript.OP_CODESEPARATOR ∨ BitcoinScript.allTrue s.st.vfExec = false)
    (h : BitcoinScriptV2.stepV2 f v o s (i, r) = some s') :
    s'.scriptCode = s.scriptCode := by sorry
