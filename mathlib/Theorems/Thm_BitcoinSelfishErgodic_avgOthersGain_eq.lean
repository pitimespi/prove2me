import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.avgOthersGain_eq (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishErgodic.avgOthersGain α γ n =
      BitcoinSelfishErgodic.expOthersGain α γ
        (BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta .zero) n) := by sorry
