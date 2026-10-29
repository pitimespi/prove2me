import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinScript
open BitcoinFunding BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinFunding.funding_witness (f : Flags) (o : Oracle) (pubkey1 pubkey2 sig1 sig2 dummy : Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.evalScript f o [sig2, sig1, dummy] (BitcoinFunding.fundingScript pubkey1 pubkey2) =
      match BitcoinScript.multisigLoop o [sig2, sig1] [pubkey2, pubkey1] with
      | none => none
      | some ok => if f.nulldummy && !dummy.isEmpty then none else some [BitcoinScript.boolBytes ok] := by sorry
