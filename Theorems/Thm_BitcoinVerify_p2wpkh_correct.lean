import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.p2wpkh_correct (tap : TaprootHandler) (c : Ctx) (sig pk h : Bytes)
    (hf : c.flags.witness = true) (hh : h.length = 20)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 h) [sig, pk] = true ↔
      BitcoinScript.castToBool h = true ∧ BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
        (BitcoinSig.p2pkhBytes h) sig pk = some true := by sorry
