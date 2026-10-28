import Definitions.Def_BitcoinMalleability
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinMalleability BitcoinSer BitcoinBlockV2

theorem BitcoinMalleability.p2sh_wrapped_scriptSig (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (sig spk : BitcoinSer.Bytes) (w : List BitcoinSer.Bytes) (hp : c.flags.p2sh = true) (hf : c.flags.witness = true)
    (hspk : BitcoinVerify.isPayToScriptHash spk = true) (hw : w ≠ [])
    (hv : BitcoinVerify.verifyScript tap c sig spk w = true) :
    ∃ redeem rest, BitcoinVerify.evalBytes c .base [] sig = some (redeem :: rest) ∧
      BitcoinVerify.isWitnessProgram redeem ≠ none ∧ sig = BitcoinSig.pushBytes redeem := by sorry
