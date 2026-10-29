import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinToLocal
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.cheater_delay_in_tx_terms (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K)
    (hN : BitcoinPenalty.NoRevocationSig (BitcoinPenalty.oracleOf c (BitcoinPenalty.toLocalBytes K)) K)
    (ws : List BitcoinSer.Bytes)
    (hv : BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toLocalBytes K))
      (ws ++ [BitcoinPenalty.toLocalBytes K]) = true)
    (hseq : BitcoinToLocal.inputSequence c.tx c.nIn < 2 ^ 16) :
    2 ≤ c.tx.version ∧ K.toSelfDelay.toNat ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by sorry
