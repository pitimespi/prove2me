import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgPoolGain_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) :
    Filter.Tendsto (BitcoinSelfishErgodic.avgPoolGain α γ) Filter.atTop
      (nhds (BitcoinSelfishMining.poolRevenue α γ)) := by sorry
