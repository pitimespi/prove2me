import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.improves_total_fee (old new : List FeeFrac) (hold : SizesPos old)
    (hnew : SizesPos new) (h : ImprovesFeerateDiagram old new) :
    diagramFee old ≤ diagramFee new := by sorry
