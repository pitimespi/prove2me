import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgRelativeRevenue_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgRelativeRevenue α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.relativeRevenue α γ)) := by sorry
