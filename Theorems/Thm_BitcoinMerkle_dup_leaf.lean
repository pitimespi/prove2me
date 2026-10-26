import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.dup_leaf {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (l : List H) (a : H) (hne : l ≠ []) (heven : l.length % 2 = 0) :
    (BitcoinMerkle.computeMerkleRoot c z (l ++ [a])).1 = (BitcoinMerkle.computeMerkleRoot c z (l ++ [a, a])).1 ∧
    (BitcoinMerkle.computeMerkleRoot c z (l ++ [a, a])).2 = true := by sorry
