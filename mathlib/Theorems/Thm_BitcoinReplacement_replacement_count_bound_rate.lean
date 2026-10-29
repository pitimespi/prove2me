import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.replacement_count_bound_rate (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    Rs.length * rate.fee ≤ ((BitcoinReplacement.chainEnd t₀ Rs).fee - t₀.fee) * rate.size := by sorry
