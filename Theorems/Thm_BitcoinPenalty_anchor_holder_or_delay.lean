import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.anchor_holder_or_delay (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (fk : BitcoinSer.Bytes) (hfk : fk = K.fundingKeyLocal ∨ fk = K.fundingKeyRemote) (ws : List BitcoinSer.Bytes) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinAnchors.anchorBytes fk))
        (ws ++ [BitcoinAnchors.anchorBytes fk]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinAnchors.anchorBytes fk)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      ∃ sig, ws = [sig] ∧
        ((BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)).checkSig sig fk = some true ∨
          ((BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)).checkSig sig fk = some false ∧
            BitcoinToLocal.CsvPasses (BitcoinVerify.scriptFlagsOf c.flags)
              (BitcoinPenalty.oracleOf c (BitcoinAnchors.anchorBytes fk)) 16)) := by sorry
