import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinFunding BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinFunding.funding_p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (pubkey1 pubkey2 : Bytes) (ws : List Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinFunding.fundingBytes pubkey1 pubkey2)))
        (ws ++ [BitcoinFunding.fundingBytes pubkey1 pubkey2]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinFunding.fundingBytes pubkey1 pubkey2)) = true ∧
      (∀ e ∈ ws, e.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) ∧
      BitcoinFunding.FundingSpend (BitcoinVerify.scriptFlagsOf c.flags)
        (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 (BitcoinFunding.fundingBytes pubkey1 pubkey2))
        pubkey1 pubkey2 ws.reverse := by sorry
