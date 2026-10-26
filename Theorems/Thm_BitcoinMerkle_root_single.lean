import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.root_single {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a : H) :
    BitcoinMerkle.computeMerkleRoot c z [a] = (a, false) := by sorry
