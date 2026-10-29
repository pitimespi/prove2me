import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.offered_timeout (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash x localSig remoteSig dummy : Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hb : o.hash160 x ≠ revHash) (h32 : x.length ≠ 32) :
    BitcoinScript.evalScript f o [x, localSig, remoteSig, dummy] (BitcoinHtlc.offeredScript revHash remoteKey localKey payHash) =
      match BitcoinScript.multisigLoop o [localSig, remoteSig] [localKey, remoteKey] with
      | none => none
      | some ok => if f.nulldummy && !dummy.isEmpty then none else some [BitcoinScript.boolBytes ok] := by sorry
