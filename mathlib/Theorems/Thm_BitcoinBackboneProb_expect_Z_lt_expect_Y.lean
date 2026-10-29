import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Z_lt_expect_Y (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (hδ : 0 < δ) (hn : 0 < n) (hp0 : 0 < (p : ℝ))
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) < ∫ ω, (Y ω r : ℝ) ∂(P n t p) := by sorry
