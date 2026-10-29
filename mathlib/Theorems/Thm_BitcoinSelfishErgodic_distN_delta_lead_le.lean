import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.distN_delta_lead_le (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (t : BitcoinSelfishMining.State) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ,
      BitcoinSelfishErgodic.distN α γ (BitcoinSelfishErgodic.delta t) n (.lead m) ≤
        C * (α / (1 - α)) ^ m := by sorry
