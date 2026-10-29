import Definitions.Def_BitcoinBackbone

theorem BitcoinBackbone.uniquely_successful_height (E : BitcoinBackbone.Execution) (hE : E.Legal)
    (i m : ℕ) (hm : m < E.n) (hmi : E.mined m i = true) (hY : E.Y i = 1)
    (C : BitcoinBackbone.Chain) (hC : E.ValidChain C) (t : ℕ) (ht : t < C.length)
    (hti : t = (E.base m i).length) (q s : ℕ) (h : C[t] = BitcoinBackbone.Block.honest q s) :
    q = m ∧ s = i := by sorry
