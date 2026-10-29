import Definitions.Def_BitcoinTapSoundness
import Theorems.Thm_BitcoinSer_sha256_length

open BitcoinTapSoundness BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

/-- The `TapLeaf` and `TapBranch` tags hash differently. -/
theorem solution :
    BitcoinSer.sha256 (BitcoinSig.ascii "TapLeaf") ≠ BitcoinSer.sha256 (BitcoinSig.ascii "TapBranch") := by
  decide +kernel
