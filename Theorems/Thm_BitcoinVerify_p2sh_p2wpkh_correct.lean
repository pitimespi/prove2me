import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinSer
open BitcoinVerify BitcoinSer BitcoinSig
open BitcoinScript hiding Bytes Byte

theorem BitcoinVerify.p2sh_p2wpkh_correct (tap : TaprootHandler) (c : Ctx) (sig pk h : Bytes)
    (hp : c.flags.p2sh = true) (hf : c.flags.witness = true) (hh : h.length = 20)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c (BitcoinSig.pushBytes (BitcoinVerify.witnessBytes 0 h))
        (BitcoinVerify.p2shBytes (BitcoinSer.hash160 (BitcoinVerify.witnessBytes 0 h))) [sig, pk] = true ↔
      BitcoinScript.castToBool h = true ∧ BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
        (BitcoinSig.p2pkhBytes h) sig pk = some true := by sorry
