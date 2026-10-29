import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.min_direct_feerate_lt (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (hne : R.direct ≠ 0) :
    ∃ t ∈ R.direct, (∀ s ∈ R.direct, t.feeRateQ ≤ s.feeRateQ) ∧
      t.feeRateQ < R.new.feeRateQ := by sorry
