import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.balance_lead_of (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ)
    (h : BitcoinSelfishUnique.IsStationary α γ π) (n : ℕ) :
    π (.lead (n + 2)) = α * π (.lead (n + 1)) + (1 - α) * π (.lead (n + 3)) := by sorry
