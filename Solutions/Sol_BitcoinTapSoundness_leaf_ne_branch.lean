import Definitions.Def_BitcoinTapSoundness
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinTapSoundness_tagged_collision
import Theorems.Thm_BitcoinTapSoundness_tapleaf_ne_tapbranch

open BitcoinTapSoundness BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

/-- A leaf hash equal to a branch hash is a SHA-256 collision. -/
theorem solution (v : BitcoinSer.Byte) (s a b : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tapleafHash v s = BitcoinTaproot.tapbranchHash a b) : BitcoinTapSoundness.Sha256Collision := by
  simp only [tapleafHash, tapbranchHash] at h
  rcases BitcoinTapSoundness.tagged_collision _ _ _ _ h with ⟨ht, -⟩ | hc
  · exact absurd ht BitcoinTapSoundness.tapleaf_ne_tapbranch
  · exact hc
