import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.offered_revocation (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash pk sig : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hb : o.hash160 pk = revHash) :
    BitcoinScript.evalScript f o [pk, sig] (BitcoinAnchors.offeredScript revHash remoteKey localKey payHash) =
      (o.checkSig sig pk).map (fun ok => [BitcoinScript.boolBytes ok]) := by sorry
