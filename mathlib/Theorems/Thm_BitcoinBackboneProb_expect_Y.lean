import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Y (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Y ω r : ℝ) ∂(P n t p) = n * p * (1 - (p : ℝ)) ^ (n - 1) := by sorry
