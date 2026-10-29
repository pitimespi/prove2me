import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.replacement_count_bound (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + Rs.length * rate.getFee 1 ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
