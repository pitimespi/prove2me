import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.pinning_cost (rate : BitcoinReplacement.FeeRate)
    (t : BitcoinReplacement.Tx) (D : Multiset BitcoinReplacement.Tx)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (hD : t ::ₘ D ≤ R.evicted) :
    t.fee + BitcoinReplacement.totalFee D + rate.getFee R.new.vsize ≤ R.new.fee := by sorry
