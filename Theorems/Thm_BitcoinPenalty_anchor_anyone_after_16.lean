import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.anchor_anyone_after_16 (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcsv : c.flags.csv = true) (K : BitcoinPenalty.CommitmentKeys)
    (hK : BitcoinPenalty.WellFormed K) (fk : BitcoinSer.Bytes) (hfk : fk = K.fundingKeyLocal ∨ fk = K.fundingKeyRemote)
    (hseq : BitcoinToLocal.inputSequence c.tx c.nIn < 2 ^ 16) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinAnchors.anchorBytes fk))
        [[], BitcoinAnchors.anchorBytes fk] = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fk)) = true ∧
      2 ≤ c.tx.version ∧ 16 ≤ BitcoinToLocal.inputSequence c.tx c.nIn := by sorry
