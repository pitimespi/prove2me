import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.to_local_penalty_sig (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toLocalBytes K)) = true)
    (sigR : BitcoinSer.Bytes) (hlen : sigR.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hsig : (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)).checkSig sigR K.revPk = some true) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true := by sorry
