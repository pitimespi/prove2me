import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typicalOn_failure_le_of_window (n t : ℕ) (p : unitInterval)
    (lam L : ℕ) (hlam : 1 ≤ lam) (β : ℝ)
    (hβ : ∀ a k : ℕ, lam ≤ k → (P n t p).real
      {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤ β) :
    (P n t p).real {ω | ¬ TypicalOn ω lam L} ≤ (L : ℝ) ^ 2 * β := by sorry
