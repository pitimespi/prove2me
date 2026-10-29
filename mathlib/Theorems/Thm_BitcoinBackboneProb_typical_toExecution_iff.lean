import Definitions.Def_BitcoinBackboneProb
import Definitions.Def_BitcoinBackbone
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typical_toExecution_iff {n t : ℕ} (ω : Trace n t) (lam L : ℕ)
    (base advParent : ℕ → ℕ → BitcoinBackbone.Chain) :
    (toExecution ω L base advParent).Typical lam ↔ TypicalTrunc ω lam L := by sorry
