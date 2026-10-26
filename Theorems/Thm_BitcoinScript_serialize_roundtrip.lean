import Definitions.Def_BitcoinScript

theorem BitcoinScript.serialize_roundtrip (n : Int) : BitcoinScript.setVch (BitcoinScript.serialize n) = n := by sorry
