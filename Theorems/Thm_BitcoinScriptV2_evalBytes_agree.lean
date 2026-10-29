import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.evalBytes_agree (c : BitcoinVerify.Ctx) (v : BitcoinSig.SigVersion)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes) (h : BitcoinScriptV2.EvalOk c v stack script) :
    BitcoinScriptV2.evalBytesV2 c v stack script = BitcoinVerify.evalBytes c v stack script := by sorry
