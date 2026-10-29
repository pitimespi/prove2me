import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Y_sub_expect_Z (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Y ω r : ℝ) ∂(P n t p) - ∫ ω, (Z ω r : ℝ) ∂(P n t p) = margin n t p := by sorry
