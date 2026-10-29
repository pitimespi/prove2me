import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typicalOn_prob_ge (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 1 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    1 - (L : ℝ) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) ≤
      (P n t p).real {ω | TypicalOn ω lam L} := by sorry
