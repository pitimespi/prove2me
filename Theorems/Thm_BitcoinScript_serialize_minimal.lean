import Definitions.Def_BitcoinScript

theorem BitcoinScript.serialize_minimal (n : Int) : BitcoinScript.nonMinimal (BitcoinScript.serialize n) = false := by sorry
