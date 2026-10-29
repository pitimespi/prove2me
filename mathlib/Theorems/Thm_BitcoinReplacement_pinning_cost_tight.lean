import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.pinning_cost_tight (rate : BitcoinReplacement.FeeRate)
    (t : BitcoinReplacement.Tx) (D : Multiset BitcoinReplacement.Tx)
    (R : BitcoinReplacement.Replacement) (hE : R.evicted = t ::ₘ D) :
    BitcoinReplacement.PaysForRBF rate R ↔
      t.fee + BitcoinReplacement.totalFee D + rate.getFee R.new.vsize ≤ R.new.fee := by sorry
