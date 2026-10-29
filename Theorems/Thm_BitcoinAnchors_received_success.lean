import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.received_success (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash preimage localSig remoteSig dummy : Bytes)
    (expiry : Int)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : expiry.natAbs < 2 ^ 32) (hb : o.hash160 preimage ≠ revHash) (h32 : preimage.length = 32) :
    BitcoinScript.evalScript f o [preimage, localSig, remoteSig, dummy]
        (BitcoinAnchors.receivedScript revHash remoteKey localKey payHash expiry) =
      if o.hash160 preimage = payHash ∧ BitcoinToLocal.CsvPasses f o 1 then
        match BitcoinScript.multisigLoop o [localSig, remoteSig] [localKey, remoteKey] with
        | none => none
        | some ok => if f.nulldummy && !dummy.isEmpty then none else some [BitcoinScript.boolBytes ok]
      else none := by sorry
