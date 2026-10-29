import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.bandwidth_paid_rate (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee * rate.size + rate.fee * (BitcoinReplacement.chainVsizes Rs).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee * rate.size := by sorry
