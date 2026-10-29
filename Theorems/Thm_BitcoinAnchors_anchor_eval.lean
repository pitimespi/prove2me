import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_eval (f : Flags) (o : Oracle) (fundingKey sig : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.anchorScript fundingKey) =
      match o.checkSig sig fundingKey with
      | none => none
      | some true => some [[1]]
      | some false => if BitcoinToLocal.CsvPasses f o 16 then some [[16]] else none := by sorry
