import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.threshold_gamma_zero (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.relativeRevenue α 0 > α ↔ α > 1 / 3 := by sorry
