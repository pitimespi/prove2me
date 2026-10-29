import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.pool_revenue_eq (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.poolRevenue α γ =
      BitcoinSelfishMining.stationary α .tie * (α * 2 + γ * (1 - α) * 1)
        + BitcoinSelfishMining.stationary α (.lead 1) * ((1 - α) * 2)
        + (∑' n : ℕ, BitcoinSelfishMining.stationary α (.lead (n + 2))) * ((1 - α) * 1) := by sorry
