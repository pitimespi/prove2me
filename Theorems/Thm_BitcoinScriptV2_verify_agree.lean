import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.verify_agree (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (scriptSig scriptPubKey : BitcoinScript.Bytes) (witness : List BitcoinScript.Bytes)
    (h1 : BitcoinScriptV2.EvalOk c .base [] scriptSig)
    (h2 : ∀ st, BitcoinScriptV2.evalBytesV2 c .base [] scriptSig = some st → BitcoinScriptV2.EvalOk c .base st scriptPubKey)
    (h3 : ∀ redeem rest, BitcoinScriptV2.evalBytesV2 c .base [] scriptSig = some (redeem :: rest) →
      BitcoinScriptV2.EvalOk c .base rest redeem)
    (h4 : ∀ script, witness.getLast? = some script → BitcoinScriptV2.EvalOk c .witnessV0 witness.dropLast.reverse script) :
    BitcoinScriptV2.verifyScriptV2 tap c scriptSig scriptPubKey witness =
      BitcoinVerify.verifyScript tap c scriptSig scriptPubKey witness := by sorry
