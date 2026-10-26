import Definitions.Def_BitcoinSer

theorem BitcoinSer.serBlock_injective (b₁ b₂ : Block) (h₁ : b₁.wf) (h₂ : b₂.wf)
    (h : BitcoinSer.serBlock true b₁ = BitcoinSer.serBlock true b₂) : b₁ = b₂ := by sorry
