import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Z_add_le_expect_Y (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) + δ * p * n / 2 ≤ ∫ ω, (Y ω r : ℝ) ∂(P n t p) := by sorry
