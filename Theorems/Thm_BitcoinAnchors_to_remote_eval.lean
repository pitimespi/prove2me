import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.to_remote_eval (f : Flags) (o : Oracle) (remoteKey sig : Bytes)
    (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.toRemoteScript remoteKey) =
      if o.checkSig sig remoteKey = some true ∧ BitcoinToLocal.CsvPasses f o 1 then some [[1]] else none := by sorry
