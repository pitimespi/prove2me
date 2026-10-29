import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.bandwidth_paid_real (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    (t₀.fee : ℚ) + ((rate.fee : ℚ) / rate.size) * (BitcoinReplacement.chainVsizes Rs).sum ≤
      ((BitcoinReplacement.chainEnd t₀ Rs).fee : ℚ) := by sorry
