import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.replacement_count_bound_min_vsize (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) (m : ℕ) (hm : ∀ R ∈ Rs, m ≤ R.new.vsize) :
    t₀.fee + Rs.length * rate.getFee m ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by sorry
