import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.le_one_of_isDist (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : BitcoinSelfishErgodic.IsDist μ) (s : BitcoinSelfishMining.State) : μ s ≤ 1 := by sorry
