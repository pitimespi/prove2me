import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinFunding BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinFunding.parseScript_funding (pubkey1 pubkey2 : Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinSig.parseScript (BitcoinFunding.fundingBytes pubkey1 pubkey2) = some (BitcoinFunding.fundingScript pubkey1 pubkey2) := by sorry
