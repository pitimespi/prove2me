import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_mass (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    BitcoinSelfishMining.stateSum (BitcoinSelfishErgodic.dist α γ μ) =
      BitcoinSelfishMining.stateSum μ := by sorry
