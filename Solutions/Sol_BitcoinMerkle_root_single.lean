import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

/-- Loop exit. -/
private theorem rootLoop_stop {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : ¬ 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = (hs.headD z, m) := by
  rw [rootLoop, dif_neg h]

theorem solution {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a : H) :
    BitcoinMerkle.computeMerkleRoot c z [a] = (a, false) := by
  unfold computeMerkleRoot
  rw [rootLoop_stop c z [a] false (by simp)]
  rfl
