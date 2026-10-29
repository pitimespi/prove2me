import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.integral_advCount (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (advCount ρ : ℝ) ∂(roundMeasure n t p) = t * p := by sorry
