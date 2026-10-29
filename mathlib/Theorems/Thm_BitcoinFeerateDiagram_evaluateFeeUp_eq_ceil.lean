import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.evaluateFeeUp_eq_ceil (f : FeeFrac) (atSize : ℤ)
    (hs : 0 < f.size) (_ha : 0 ≤ atSize) :
    FeeFrac.evaluateFeeUp f atSize = ⌈((f.fee * atSize : ℤ) : ℚ) / f.size⌉ := by sorry
