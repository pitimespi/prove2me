import Definitions.Def_BitcoinPenalty
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinPenalty BitcoinToLocal BitcoinHtlc BitcoinAnchors BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinPenalty.to_remote_honest_only (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (K : BitcoinPenalty.CommitmentKeys) (hK : BitcoinPenalty.WellFormed K)
    (ws : List BitcoinSer.Bytes) :
    BitcoinVerify.verifyScript tap c [] (BitcoinPenalty.p2wshOf (BitcoinPenalty.toRemoteBytes K))
        (ws ++ [BitcoinPenalty.toRemoteBytes K]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinPenalty.toRemoteBytes K)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      ∃ sig, ws = [sig] ∧
        (BitcoinPenalty.oracleOf c (BitcoinPenalty.toRemoteBytes K)).checkSig sig K.remoteKey = some true ∧
        BitcoinToLocal.CsvPasses (BitcoinVerify.scriptFlagsOf c.flags)
          (BitcoinPenalty.oracleOf c (BitcoinPenalty.toRemoteBytes K)) 1 := by sorry
