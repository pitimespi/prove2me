import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.paysForRBF_iff (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) :
    BitcoinReplacement.PaysForRBF rate R ↔
      BitcoinReplacement.totalFee R.evicted + rate.getFee R.new.vsize ≤ R.new.fee := by sorry
