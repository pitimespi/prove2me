import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgOthersGain_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgOthersGain α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.othersRevenue α γ)) := by sorry
