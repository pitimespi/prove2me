import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_nonneg (α γ : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (μ : BitcoinSelfishMining.State → ℝ) (hμ : ∀ s, 0 ≤ μ s) (s : BitcoinSelfishMining.State) :
    0 ≤ BitcoinSelfishErgodic.dist α γ μ s := by sorry
