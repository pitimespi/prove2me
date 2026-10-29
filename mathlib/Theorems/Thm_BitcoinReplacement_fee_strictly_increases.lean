import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.fee_strictly_increases (rate : BitcoinReplacement.FeeRate)
    (hr : 0 < rate.fee) (R : BitcoinReplacement.Replacement)
    (hR : BitcoinReplacement.Valid rate R) (t : BitcoinReplacement.Tx) (ht : t ∈ R.evicted) :
    t.fee < R.new.fee := by sorry
