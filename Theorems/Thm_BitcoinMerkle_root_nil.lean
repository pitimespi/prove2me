import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.root_nil {H : Type} [DecidableEq H] (c : H → H → H) (z : H) :
    BitcoinMerkle.computeMerkleRoot c z [] = (z, false) := by sorry
