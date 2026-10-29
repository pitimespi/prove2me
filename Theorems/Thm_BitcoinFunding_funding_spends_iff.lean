import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinVerify
open BitcoinFunding BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinFunding.funding_spends_iff (f : Flags) (o : Oracle) (pubkey1 pubkey2 : Bytes) (st : List Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinFunding.fundingScript pubkey1 pubkey2) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      BitcoinFunding.FundingSpend f o pubkey1 pubkey2 st := by sorry
