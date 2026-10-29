import Definitions.Def_BitcoinSelfishMining

/-!
# Selfish mining: stationary distributions of the Eyal–Sirer chain

This file defines what it means for a function `π : State → ℝ` to be a stationary distribution of
the selfish-mining chain of `Definitions/Def_BitcoinSelfishMining.lean`: it is nonnegative, its
values on the leads form a summable family (so that `stateSum π` is a genuine sum), it has total
mass one and it is invariant under one step of the chain, `π s = Σ_t π t · P(t → s)` for every
state `s` (the sum running over all states via `stateSum`).

The paper's distribution `stationary α` is one such distribution (`stationary_balance`,
`total_mass` in the solutions of `BitcoinSelfishMining`); the theorems in
`Solutions/Sol_BitcoinSelfishUnique_all.lean` show that for `0 < α < 1/2` it is the only one.
-/

namespace BitcoinSelfishUnique

/-- A stationary distribution of the selfish-mining chain: nonnegative, summable over the leads,
total mass one, invariant under one step. -/
structure IsStationary (α γ : ℝ) (π : BitcoinSelfishMining.State → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ π s
  summable : Summable (fun n : ℕ => π (.lead n))
  mass : BitcoinSelfishMining.stateSum π = 1
  invariant : ∀ s, π s = BitcoinSelfishMining.stateSum (fun t => π t * BitcoinSelfishMining.P α γ t s)

end BitcoinSelfishUnique
