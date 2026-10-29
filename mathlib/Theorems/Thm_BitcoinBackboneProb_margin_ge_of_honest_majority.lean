import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.margin_ge_of_honest_majority (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) :
    δ * p * n / 2 ≤ margin n t p := by sorry
