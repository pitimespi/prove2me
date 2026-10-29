import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.window_bound_rate (n t : ℕ) (p : unitInterval) (a k : ℕ)
    (hk1 : 1 ≤ k) (hm : 0 < margin n t p) (hk : 4 * t * (p : ℝ) ≤ ((k : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤
      Real.exp (-rate n t p * ((k : ℝ) + 1)) := by sorry
