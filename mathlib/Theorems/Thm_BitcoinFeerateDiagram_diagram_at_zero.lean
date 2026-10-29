import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.diagram_at_zero {cs : List FeeFrac} (h : SizesPos cs) :
    diagram cs 0 = 0 := by sorry
