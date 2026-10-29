import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.map_eval_P (n t : ℕ) (p : unitInterval) (r : ℕ) :
    (P n t p).map (fun ω => ω r) = roundMeasure n t p := by sorry
