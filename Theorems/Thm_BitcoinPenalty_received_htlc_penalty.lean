import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.received_htlc_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.receivedBytes K h)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
      (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytes K h)) = true := by sorry
