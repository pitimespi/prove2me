import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.offered_htlc_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hh : BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.offeredBytes K h)) = true)
    (hR : BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K) :
    ∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
      (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytes K h)) = true := by sorry
