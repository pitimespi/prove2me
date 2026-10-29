import Definitions.Def_BitcoinTapSoundnessV2
import Theorems.Thm_BitcoinSer_sha256_length

open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

/-- A tagged hash is the SHA-256 of its preimage `taggedPre`. -/
theorem solution (t : String) (m : BitcoinSer.Bytes) :
    BitcoinTaproot.tagged t m = BitcoinSer.sha256 (BitcoinTapSoundnessV2.taggedPre t m) := by
  rfl
