import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typicalOn_failure_le (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 1 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ¬ TypicalOn ω lam L} ≤
      (L : ℝ) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by sorry
