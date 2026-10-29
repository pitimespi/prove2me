import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.evaluateFeeDown_eq_floor (f : FeeFrac) (atSize : ℤ)
    (hs : 0 < f.size) (_ha : 0 ≤ atSize) :
    FeeFrac.evaluateFeeDown f atSize = ⌊((f.fee * atSize : ℤ) : ℚ) / f.size⌋ := by sorry
