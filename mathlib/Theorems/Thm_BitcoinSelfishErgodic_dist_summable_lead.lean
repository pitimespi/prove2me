import Definitions.Def_BitcoinSelfishErgodic
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

theorem BitcoinSelfishErgodic.dist_summable_lead (α γ : ℝ) (μ : BitcoinSelfishMining.State → ℝ)
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    Summable (fun n : ℕ => BitcoinSelfishErgodic.dist α γ μ (.lead n)) := by sorry
