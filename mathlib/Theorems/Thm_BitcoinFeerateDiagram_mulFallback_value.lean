import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.mulFallback_value (a b : ℤ) :
    (FeeFrac.mulFallback a b).1 * 2 ^ 32 + (FeeFrac.mulFallback a b).2 = FeeFrac.mul a b := by sorry
