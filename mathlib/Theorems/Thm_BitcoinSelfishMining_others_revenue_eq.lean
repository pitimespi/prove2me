import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.others_revenue_eq (α γ : ℝ) :
    BitcoinSelfishMining.othersRevenue α γ =
      BitcoinSelfishMining.stationary α .tie * ((1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1)
        + BitcoinSelfishMining.stationary α .zero * ((1 - α) * 1) := by sorry
