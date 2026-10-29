import Definitions.Def_BitcoinSelfishUnique
import Definitions.Def_BitcoinSelfishMining
open BitcoinSelfishUnique BitcoinSelfishMining

theorem BitcoinSelfishUnique.geometric_of_isStationary (α γ : ℝ)
    (π : BitcoinSelfishMining.State → ℝ) (h0 : 0 < α) (h1 : α < 1 / 2)
    (h : BitcoinSelfishUnique.IsStationary α γ π) (n : ℕ) :
    π (.lead (n + 1)) = α / (1 - α) * π (.lead n) := by sorry
