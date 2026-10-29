import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.diagram_concave (cs : List FeeFrac) (hpos : SizesPos cs)
    (hsort : FeeratesNonIncreasing cs) :
    ConcaveOn ℚ (Set.Icc 0 (diagramSize cs : ℚ)) (diagram cs) := by sorry
