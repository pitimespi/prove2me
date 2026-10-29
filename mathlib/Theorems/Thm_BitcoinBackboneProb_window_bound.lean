import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.window_bound (n t : ℕ) (p : unitInterval) (a k : ℕ) (hk1 : 1 ≤ k)
    (hk : 2 * t * (p : ℝ) ≤ ((k : ℝ) - 1) * margin n t p) :
    (P n t p).real {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤
      Real.exp (-2 * (((k : ℝ) - 1) * margin n t p - 2 * t * p) ^ 2 /
        (((k : ℝ) + 1) * ((t : ℝ) + 1) ^ 2)) := by sorry
