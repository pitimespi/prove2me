import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.threshold (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    BitcoinSelfishMining.relativeRevenue α γ > α ↔ α > BitcoinSelfishMining.profitThreshold γ := by sorry
