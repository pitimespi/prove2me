import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.diagram_total {cs : List FeeFrac} (h : SizesPos cs) {x : ℚ}
    (hx : (diagramSize cs : ℚ) ≤ x) : diagram cs x = diagramFee cs := by sorry
