import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.received_revocation (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash pk sig : Bytes) (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hb : o.hash160 pk = revHash) :
    BitcoinScript.evalScript f o [pk, sig] (BitcoinHtlc.receivedScript revHash remoteKey localKey payHash expiry) =
      (o.checkSig sig pk).map (fun ok => [BitcoinScript.boolBytes ok]) := by sorry
