import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.runOk_of_static (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (l : List (BitcoinScript.Instr × BitcoinScript.Bytes)) (s : BitcoinScriptV2.StateV2)
    (h1 : BitcoinScriptV2.NoCodeSep (l.map Prod.fst)) (h2 : BitcoinScriptV2.NoMultisig (l.map Prod.fst)) :
    BitcoinScriptV2.RunOk f v o s l := by sorry
