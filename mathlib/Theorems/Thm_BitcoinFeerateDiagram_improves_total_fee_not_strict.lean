import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.improves_total_fee_not_strict :
    ∃ old new : List FeeFrac, SizesPos old ∧ SizesPos new ∧ FeeratesNonIncreasing old ∧
      FeeratesNonIncreasing new ∧ ImprovesFeerateDiagram old new ∧
      diagramFee old = diagramFee new := by sorry
