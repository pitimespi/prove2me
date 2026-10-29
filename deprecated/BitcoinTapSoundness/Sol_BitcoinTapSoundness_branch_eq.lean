import Definitions.Def_BitcoinTapSoundness
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinTapSoundness_tagged_collision

open BitcoinTapSoundness BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

/-- Equal branch hashes of 32-byte children have the same two children (in some order), or exhibit
a collision. -/
theorem solution (a b c d : BitcoinSer.Bytes) (ha : a.length = 32) (hb : b.length = 32)
    (hc : c.length = 32) (hd : d.length = 32) (h : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash c d) :
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∨ BitcoinTapSoundness.Sha256Collision := by
  simp only [tapbranchHash] at h
  rcases BitcoinTapSoundness.tagged_collision _ _ _ _ h with ⟨-, hm⟩ | hcol
  · left
    split at hm <;> split at hm
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [ha, hc]) hm; exact Or.inl ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [ha, hd]) hm; exact Or.inr ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [hb, hc]) hm; exact Or.inr ⟨h2, h1⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [hb, hd]) hm; exact Or.inl ⟨h2, h1⟩
  · right; exact hcol
