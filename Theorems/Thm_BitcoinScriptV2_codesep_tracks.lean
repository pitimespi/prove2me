import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.codesep_tracks (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (script : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (hl : BitcoinScriptV2.annotate script = some l) (k : Nat) (r : BitcoinScript.Bytes)
    (hk : l[k]? = some (.op BitcoinScript.OP_CODESEPARATOR, r))
    (s s' : BitcoinScriptV2.StateV2) (hexec : BitcoinScript.allTrue s.st.vfExec = true)
    (h : BitcoinScriptV2.stepV2 f v o s (.op BitcoinScript.OP_CODESEPARATOR, r) = some s') :
    s'.scriptCode = r ∧ ∃ p, script[p]? = some BitcoinScript.OP_CODESEPARATOR ∧ r = script.drop (p + 1) := by sorry
