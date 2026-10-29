import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.tail_sum (α : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    ∑' n : ℕ, BitcoinSelfishMining.stationary α (.lead (n + 2)) =
      BitcoinSelfishMining.stationary α (.lead 0) * (α / (1 - α)) ^ 2 * (1 - α) / (1 - 2 * α) := by sorry
