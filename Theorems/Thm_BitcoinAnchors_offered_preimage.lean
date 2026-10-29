import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.offered_preimage (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash preimage sig : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hb : o.hash160 preimage ≠ revHash) (h32 : preimage.length = 32) :
    BitcoinScript.evalScript f o [preimage, sig] (BitcoinAnchors.offeredScript revHash remoteKey localKey payHash) =
      if o.hash160 preimage = payHash ∧ BitcoinToLocal.CsvPasses f o 1 then
        (o.checkSig sig remoteKey).map (fun ok => [BitcoinScript.boolBytes ok])
      else none := by sorry
