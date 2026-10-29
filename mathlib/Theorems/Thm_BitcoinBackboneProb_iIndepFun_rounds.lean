import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.iIndepFun_rounds (n t : ℕ) (p : unitInterval) :
    ProbabilityTheory.iIndepFun (fun r (ω : Trace n t) => ω r) (P n t p) := by sorry
