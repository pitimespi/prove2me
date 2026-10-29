import Definitions.Def_BitcoinFeerateDiagram
open BitcoinFeerateDiagram BitcoinReplacement

theorem BitcoinFeerateDiagram.no_free_relay_diagram (rate : FeeRate) (R : Replacement)
    (old new : List FeeFrac) (F : ℤ) (hold : SizesPos old) (hnew : SizesPos new)
    (hfold : diagramFee old = F + totalFee R.evicted) (hfnew : diagramFee new = F + R.new.fee)
    (himp : ImprovesFeerateDiagram old new) (hpay : PaysForRBF rate R) :
    StrictlyBetter new old ∧ diagramFee old + rate.getFee R.new.vsize ≤ diagramFee new := by sorry
