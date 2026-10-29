import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_lead_succ (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (n : ℕ) :
    BitcoinSelfishErgodic.dist α γ μ (.lead (n + 2)) =
      α * μ (.lead (n + 1)) + (1 - α) * μ (.lead (n + 3)) := by sorry
