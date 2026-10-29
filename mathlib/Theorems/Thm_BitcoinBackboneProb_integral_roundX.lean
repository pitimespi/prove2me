import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.integral_roundX (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (roundX ρ : ℝ) ∂(roundMeasure n t p) = 1 - (1 - (p : ℝ)) ^ n := by sorry
