import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.evalOk_of_static (c : BitcoinVerify.Ctx) (v : BitcoinSig.SigVersion)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes)
    (h : ∀ s, BitcoinSig.parseScript script = some s → BitcoinScriptV2.NoCodeSep s ∧ BitcoinScriptV2.NoMultisig s) :
    BitcoinScriptV2.EvalOk c v stack script := by sorry
