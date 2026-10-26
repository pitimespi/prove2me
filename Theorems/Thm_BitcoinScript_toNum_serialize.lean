import Definitions.Def_BitcoinScript

theorem BitcoinScript.toNum_serialize (n : Int) (h : (BitcoinScript.serialize n).length ≤ 4) :
    BitcoinScript.toNum true 4 (BitcoinScript.serialize n) = some n := by sorry
