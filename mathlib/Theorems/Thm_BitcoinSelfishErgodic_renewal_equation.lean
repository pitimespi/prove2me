import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.renewal_equation (α γ : ℝ) (n : ℕ) :
    BitcoinSelfishErgodic.returnProb α γ (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        BitcoinSelfishErgodic.firstPassage α γ .zero k * BitcoinSelfishErgodic.returnProb α γ (n - k) := by sorry
