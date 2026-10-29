import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.cesaro_tendsto (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ)
    (s : BitcoinSelfishMining.State) :
    Filter.Tendsto (fun n => BitcoinSelfishErgodic.cesaro α γ μ n s) Filter.atTop
      (nhds (BitcoinSelfishMining.stationary α s)) := by sorry
