import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.chain_growth (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (p q : ℕ) (hp : p < E.n) (hq : q < E.n) (r s : ℕ) (hrs : r < s) :
    (E.chain p r).length + ∑ i ∈ Finset.Ico (r + 1) s, E.X i ≤ (E.chain q s).length := by sorry
