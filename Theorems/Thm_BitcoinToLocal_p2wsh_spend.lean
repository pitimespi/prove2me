import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (rev dpk : Bytes) (delay : Int) (ws : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinToLocal.toLocalBytes rev delay dpk)))
        (ws ++ [BitcoinToLocal.toLocalBytes rev delay dpk]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinToLocal.toLocalBytes rev delay dpk)) = true ∧
      ∃ b sig, ws = [sig, b] ∧ sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE ∧ b.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE ∧
        BitcoinToLocal.SpendCondition (BitcoinVerify.scriptFlagsOf c.flags)
          (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 (BitcoinToLocal.toLocalBytes rev delay dpk))
          rev delay dpk b sig := by sorry
