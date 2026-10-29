import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.div_round_down_eq_floor (n d : ℤ) (hd : 0 < d) :
    FeeFrac.div n d true = ⌊(n : ℚ) / d⌋ := by sorry
