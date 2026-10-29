import Definitions.Def_BitcoinTapSoundness
import Theorems.Thm_BitcoinSer_sha256_length

open BitcoinTapSoundness BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

/-- Equal tagged hashes have equal tags' hashes and equal messages, or exhibit a SHA-256 collision. -/
theorem solution (t t' : String) (m m' : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tagged t m = BitcoinTaproot.tagged t' m') :
    (BitcoinSer.sha256 (BitcoinSig.ascii t) = BitcoinSer.sha256 (BitcoinSig.ascii t') ∧ m = m') ∨
      BitcoinTapSoundness.Sha256Collision := by
  simp only [tagged, BitcoinSig.taggedHash] at h
  by_cases heq : sha256 (BitcoinSig.ascii t) ++ sha256 (BitcoinSig.ascii t) ++ m =
      sha256 (BitcoinSig.ascii t') ++ sha256 (BitcoinSig.ascii t') ++ m'
  · left
    have hl : (sha256 (BitcoinSig.ascii t) ++ sha256 (BitcoinSig.ascii t)).length =
        (sha256 (BitcoinSig.ascii t') ++ sha256 (BitcoinSig.ascii t')).length := by
      simp only [List.length_append, BitcoinSer.sha256_length]
    obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ hl heq
    obtain ⟨h3, -⟩ := append_inj_len _ _ _ _ (by simp only [BitcoinSer.sha256_length]) h1
    exact ⟨h3, h2⟩
  · right; exact ⟨_, _, heq, h⟩
