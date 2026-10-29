import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.firstReturn_zero (α γ : ℝ) :
    BitcoinSelfishErgodic.firstPassage α γ .zero 0 = 1 - α := by sorry
