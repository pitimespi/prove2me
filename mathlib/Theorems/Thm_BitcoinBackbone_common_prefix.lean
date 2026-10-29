import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.common_prefix (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (lam : ℕ) (hT : E.Typical lam) (p₁ p₂ : ℕ) (hp₁ : p₁ < E.n) (hp₂ : p₂ < E.n)
    (r₁ r₂ : ℕ) (hr : r₁ ≤ r₂) :
    (E.chain p₁ r₁).take ((E.chain p₁ r₁).length - 2 * lam) <+: E.chain p₂ r₂ := by sorry
