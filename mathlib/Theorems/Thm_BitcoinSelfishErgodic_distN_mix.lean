import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.distN_mix (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : BitcoinSelfishErgodic.IsDist μ) (n : ℕ)
    (s : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.distN α γ μ n s =
      BitcoinSelfishMining.stateSum
        (fun t => μ t * BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta t) n s) := by sorry
