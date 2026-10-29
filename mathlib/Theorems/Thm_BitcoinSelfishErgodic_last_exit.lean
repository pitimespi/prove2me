import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.last_exit (α γ : ℝ) (n : ℕ) (s : BitcoinSelfishMining.State) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta .zero) n s =
      ∑ k ∈ Finset.range (n + 1),
        BitcoinSelfishErgodic.returnProb α γ k * BitcoinSelfishErgodic.taboo α γ .zero (n - k) s := by sorry
