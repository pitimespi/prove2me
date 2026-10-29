import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.balance_tie (α : ℝ) (_h0 : 0 < α) (_h1 : α < 1 / 2) :
    BitcoinSelfishMining.stationary α .tie =
      (1 - α) * BitcoinSelfishMining.stationary α (.lead 0) := by sorry
