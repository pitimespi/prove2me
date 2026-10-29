import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.offered_cheater_no_revocation (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytes K h))
      (ws ++ [BitcoinPenalty.offeredBytes K h]) = true) :
    BitcoinPenalty.OfferedNonRevocation (BitcoinVerify.scriptFlagsOf c.flags)
      (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytes K h)) K h ws.reverse := by sorry
