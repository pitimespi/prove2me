import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.getFee_eq_evaluateFeeUp (r : FeeRate) (v : ℕ) :
    (r.getFee v : ℤ) = FeeFrac.evaluateFeeUp ⟨r.fee, r.size⟩ v := by sorry
