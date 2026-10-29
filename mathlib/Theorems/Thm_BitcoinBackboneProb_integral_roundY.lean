import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.integral_roundY (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (roundY ρ : ℝ) ∂(roundMeasure n t p) = n * p * (1 - (p : ℝ)) ^ (n - 1) := by sorry
