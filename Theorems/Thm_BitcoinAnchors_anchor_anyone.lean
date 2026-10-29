import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_anyone (f : Flags) (o : Oracle) (fundingKey sig : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hcs : o.checkSig sig fundingKey = some false) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.anchorScript fundingKey) =
      if BitcoinToLocal.CsvPasses f o 16 then some [[16]] else none := by sorry
