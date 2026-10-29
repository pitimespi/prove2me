import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.divFallback_eq_div (n : ℤ × ℤ) (d : ℤ) (hd : 0 < d) (rd : Bool) :
    FeeFrac.divFallback n d rd = FeeFrac.div (n.1 * 2 ^ 32 + n.2) d rd := by sorry
