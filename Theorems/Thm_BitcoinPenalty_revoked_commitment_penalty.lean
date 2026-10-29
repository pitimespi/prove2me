import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.revoked_commitment_penalty (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hR : ∀ sc, BitcoinPenalty.HoldsRevocation (BitcoinPenalty.oracleOf c sc) K)
    (hh : ∀ sc ∈ [BitcoinPenalty.toLocalBytes K, BitcoinPenalty.offeredBytes K h, BitcoinPenalty.receivedBytes K h,
        BitcoinPenalty.offeredBytesAnchors K h, BitcoinPenalty.receivedBytesAnchors K h],
      BitcoinScript.castToBool (BitcoinSer.sha256 sc) = true) :
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
        (BitcoinPenalty.toLocalPenaltyWitness K sigR) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytes K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytes K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.offeredBytesAnchors K h)) = true) ∧
    (∃ sigR, BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytesAnchors K h))
        (BitcoinPenalty.htlcPenaltyWitness K sigR (BitcoinPenalty.receivedBytesAnchors K h)) = true) := by sorry
