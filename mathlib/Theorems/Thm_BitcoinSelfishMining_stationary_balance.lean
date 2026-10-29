import Definitions.Def_BitcoinSelfishMining

theorem BitcoinSelfishMining.stationary_balance (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishMining.stationary α s =
      BitcoinSelfishMining.stateSum
        (fun t => BitcoinSelfishMining.stationary α t * BitcoinSelfishMining.P α γ t s) := by sorry
