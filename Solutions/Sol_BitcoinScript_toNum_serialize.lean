import Definitions.Def_BitcoinScript
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinScript_serialize_minimal

open BitcoinScript

theorem solution (n : Int) (h : (BitcoinScript.serialize n).length ≤ 4) :
    BitcoinScript.toNum true 4 (BitcoinScript.serialize n) = some n := by
  unfold toNum
  rw [if_neg (by omega), BitcoinScript.serialize_minimal]
  simp [BitcoinScript.serialize_roundtrip]
