import Definitions.Def_BitcoinBackboneProb
import Definitions.Def_BitcoinBackbone
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.backbone_failure_le (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 2 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p)
    (Q : BitcoinBackbone.Execution → Prop)
    (hdet : ∀ E : BitcoinBackbone.Execution, E.Legal → E.Typical lam → Q E) :
    (P n t p).real {ω | ∃ base advParent : ℕ → ℕ → BitcoinBackbone.Chain,
      (toExecution ω L base advParent).Legal ∧ ¬ Q (toExecution ω L base advParent)} ≤
      ((L : ℝ) + 1) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by sorry
