import Definitions.Def_BitcoinSelfishErgodic
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.distN_zero_lead_le (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (n m : ℕ) :
    BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta .zero) n (.lead m) ≤
      (α / (1 - α)) ^ m := by sorry
