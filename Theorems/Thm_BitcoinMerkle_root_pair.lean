import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.root_pair {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a b : H) :
    BitcoinMerkle.computeMerkleRoot c z [a, b] = (c a b, decide (a = b)) := by sorry
