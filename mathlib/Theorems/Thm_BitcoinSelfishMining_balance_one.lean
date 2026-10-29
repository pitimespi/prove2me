import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.balance_one (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α (.lead 0) =
      α * BitcoinSelfishMining.stationary α .zero := by sorry
