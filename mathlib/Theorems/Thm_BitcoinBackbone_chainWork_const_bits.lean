import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.chainWork_const_bits (S : BitcoinBlockV2.ChainState) (bits : ℕ)
    (h : ∀ hd ∈ S.headers, hd.bits = bits) :
    S.chainWork = S.headers.length * BitcoinBlockV2.blockProof bits := by sorry
