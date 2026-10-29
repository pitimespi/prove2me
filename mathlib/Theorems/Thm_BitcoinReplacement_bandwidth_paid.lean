import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.bandwidth_paid (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + ((BitcoinReplacement.chainVsizes Rs).map rate.getFee).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
