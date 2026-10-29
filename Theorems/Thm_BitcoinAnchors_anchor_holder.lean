import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinAnchors.anchor_holder (f : Flags) (o : Oracle) (fundingKey sig : Bytes)
    (hfk : fundingKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hcs : o.checkSig sig fundingKey = some true) :
    BitcoinScript.evalScript f o [sig] (BitcoinAnchors.anchorScript fundingKey) = some [[1]] := by sorry
