import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.received_cheater_height (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcltv : c.flags.cltv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K) (h : BitcoinPenalty.Htlc) (hw : BitcoinPenalty.HtlcWellFormed h)
    (hexp : 0 < h.expiry ∧ h.expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (hnIn : c.nIn < c.tx.vin.length)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K)
    (hP : BitcoinPenalty.NoRevHashPreimage (BitcoinPenalty.oracleOf c (BitcoinPenalty.receivedBytes K h)) K)
    (sig pk : BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.receivedBytes K h))
      ([sig, pk] ++ [BitcoinPenalty.receivedBytes K h]) = true)
    (height : Nat) (blockTime : Int) (hfinal : BitcoinBlockV2.isFinalTx c.tx height blockTime = true) :
    h.expiry < height := by sorry
