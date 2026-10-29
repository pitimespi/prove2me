import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSig
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.htlc_cheater_one_block_anchors (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K) (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.offeredBytesAnchors K h)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.offeredBytesAnchors K h))
      (ws ++ [BitcoinPenalty.offeredBytesAnchors K h]) = true) :
    2 ≤ c.tx.version ∧
      BitcoinToLocal.inputSequence c.tx c.nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      1 ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by sorry
