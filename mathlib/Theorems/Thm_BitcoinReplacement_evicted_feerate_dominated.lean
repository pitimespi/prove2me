import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.evicted_feerate_dominated (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (t : BitcoinReplacement.Tx) (ht : t ∈ R.direct) :
    t.fee * R.new.vsize < R.new.fee * t.vsize := by sorry
