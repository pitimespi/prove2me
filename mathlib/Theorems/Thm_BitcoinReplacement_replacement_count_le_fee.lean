import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.replacement_count_le_fee (rate : BitcoinReplacement.FeeRate)
    (hr : 0 < rate.fee) (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + Rs.length ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
