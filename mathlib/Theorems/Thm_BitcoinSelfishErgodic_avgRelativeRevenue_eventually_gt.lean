import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgRelativeRevenue_eventually_gt (α γ : ℝ) (h0 : 0 < α)
    (h1 : α < 1 / 2) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hT : α > BitcoinSelfishMining.profitThreshold γ) :
    ∀ᶠ n in Filter.atTop, α < BitcoinSelfishErgodic.avgRelativeRevenue α γ n := by sorry
