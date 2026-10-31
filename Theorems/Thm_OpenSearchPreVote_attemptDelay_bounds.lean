import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.attemptDelay_bounds (s : SchedulerSettings) (hs : s.Valid) (k : Nat) (r : Int)
    (g : Nat) :
    1 ≤ maxDelay s k ∧ g + 1 ≤ attemptDelay s k r g ∧ attemptDelay s k r g ≤ g + maxDelay s k := by sorry
