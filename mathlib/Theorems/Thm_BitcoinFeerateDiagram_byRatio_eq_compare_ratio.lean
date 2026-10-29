import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.byRatio_eq_compare_ratio (a b : FeeFrac)
    (ha : 0 < a.size) (hb : 0 < b.size) :
    FeeFrac.byRatioCmp a b = compare a.ratio b.ratio := by sorry
