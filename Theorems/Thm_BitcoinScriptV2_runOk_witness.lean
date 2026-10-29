import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.runOk_witness (f : BitcoinScript.Flags) (o : BitcoinScriptV2.OracleV2)
    (l : List (BitcoinScript.Instr × BitcoinScript.Bytes)) (s : BitcoinScriptV2.StateV2)
    (h1 : BitcoinScriptV2.NoCodeSep (l.map Prod.fst)) :
    BitcoinScriptV2.RunOk f .witnessV0 o s l := by sorry
