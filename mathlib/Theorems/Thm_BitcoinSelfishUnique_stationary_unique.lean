import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.stationary_unique (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h0 : 0 < α) (h1 : α < 1 / 2) (h : BitcoinSelfishUnique.IsStationary α γ π)
    (s : BitcoinSelfishMining.State) : π s = BitcoinSelfishMining.stationary α s := by sorry
