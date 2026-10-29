import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.annotate_parse (s : BitcoinScript.Bytes) :
    (BitcoinScriptV2.annotate s).map (List.map Prod.fst) = BitcoinSig.parseScript s := by sorry
