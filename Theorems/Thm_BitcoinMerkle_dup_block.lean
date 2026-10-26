import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.dup_block {H : Type} [DecidableEq H] (c : H → H → H) (z : H) :
    ∀ (k : Nat) (l t : List H), l ≠ [] → l.length % 2 ^ (k + 1) = 0 → t.length = 2 ^ k →
      (BitcoinMerkle.computeMerkleRoot c z (l ++ t)).1 = (BitcoinMerkle.computeMerkleRoot c z (l ++ t ++ t)).1 ∧
      (BitcoinMerkle.computeMerkleRoot c z (l ++ t ++ t)).2 = true := by sorry
