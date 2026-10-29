import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.common_prefix_rounds (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p₁ p₂ : ℕ) (hp₁ : p₁ < E.n) (hp₂ : p₂ < E.n)
    (r₁ r₂ : ℕ) (hr : r₁ ≤ r₂) (w : ℕ) (hw : lam ≤ w) (hwr : w ≤ r₁) :
    (E.chain p₁ r₁).upTo (r₁ - w) <+: E.chain p₂ r₂ := by sorry
