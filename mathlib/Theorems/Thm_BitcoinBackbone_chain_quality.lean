import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.chain_quality (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p : ℕ) (hp : p < E.n) (r u : ℕ)
    (hu : u + lam ≤ (E.chain p r).length) :
    ∃ B ∈ ((E.chain p r).drop u).take lam, B.isHonest = true := by sorry
