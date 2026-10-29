import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.common_prefix_private (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p : ℕ) (hp : p < E.n) (r : ℕ)
    (D : BitcoinBackbone.Chain) (hD : E.ValidChain D) (hDr : ∀ B ∈ D, B.round ≤ r)
    (f r₀ : ℕ) (hfD : f ≤ D.length)
    (hfork : (f = 0 ∧ r₀ = 0) ∨
      ∃ q, ∃ hf : f - 1 < D.length, 0 < f ∧ D[f - 1] = BitcoinBackbone.Block.honest q r₀)
    (hadv : ∀ k (hk : k < D.length), f ≤ k → D[k].isHonest = false)
    (hwin : r₀ + lam ≤ r) : D.length < (E.chain p r).length := by sorry
