import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.div_round_up_eq_ceil (n d : ℤ) (hd : 0 < d) :
    FeeFrac.div n d false = ⌈(n : ℚ) / d⌉ := by sorry
