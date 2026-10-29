import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_X (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (X ω r : ℝ) ∂(P n t p) = 1 - (1 - (p : ℝ)) ^ n := by sorry
