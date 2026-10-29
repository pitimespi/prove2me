import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Z (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) = t * p := by sorry
