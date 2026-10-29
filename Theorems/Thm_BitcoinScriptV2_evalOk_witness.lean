import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.evalOk_witness (c : BitcoinVerify.Ctx) (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes)
    (h : ∀ s, BitcoinSig.parseScript script = some s → BitcoinScriptV2.NoCodeSep s) :
    BitcoinScriptV2.EvalOk c .witnessV0 stack script := by sorry
