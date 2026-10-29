import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.fadAll_witness (sc : BitcoinScript.Bytes) (sigs : List BitcoinScript.Bytes) :
    BitcoinScriptV2.fadAll .witnessV0 sc sigs = sc := by sorry
