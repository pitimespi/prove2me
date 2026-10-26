import Definitions.Def_BitcoinScript

theorem BitcoinScript.castToBool_iff (v : Bytes) : BitcoinScript.castToBool v = true ↔ BitcoinScript.setVch v ≠ 0 := by sorry
