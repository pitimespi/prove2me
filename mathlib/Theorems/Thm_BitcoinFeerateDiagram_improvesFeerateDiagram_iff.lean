import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.improvesFeerateDiagram_iff (old new : List FeeFrac)
    (hold : SizesPos old) (hnew : SizesPos new) :
    ImprovesFeerateDiagram old new ↔ StrictlyBetter new old := by sorry
