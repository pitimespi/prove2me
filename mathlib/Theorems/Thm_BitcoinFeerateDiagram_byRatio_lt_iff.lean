import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.byRatio_lt_iff (a b : FeeFrac) (ha : 0 < a.size) (hb : 0 < b.size) :
    FeeFrac.byRatioCmp a b = .lt ↔ a.ratio < b.ratio := by sorry
