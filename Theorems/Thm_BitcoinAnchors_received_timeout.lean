import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.received_timeout (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x sig : Bytes) (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hb : o.hash160 x ≠ revHash) (h32 : x.length ≠ 32) :
    BitcoinScript.evalScript f o [x, sig] (BitcoinAnchors.receivedScript revHash remoteKey localKey payHash expiry) =
      if BitcoinHtlc.CltvPasses f o expiry ∧ BitcoinToLocal.CsvPasses f o 1 then
        (o.checkSig sig remoteKey).map (fun ok => [BitcoinScript.boolBytes ok])
      else none := by sorry
