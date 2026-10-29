import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.chain_growth_self (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (p : ℕ) (hp : p < E.n) (r s : ℕ) (hrs : r ≤ s) :
    (E.chain p r).length + ∑ i ∈ Finset.Ico (r + 1) s, E.X i ≤ (E.chain p s).length := by sorry
