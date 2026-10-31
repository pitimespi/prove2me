import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.randomDelay_range (M : Nat) (hM : 1 ≤ M) (x : Fin (2 ^ 64)) :
    1 ≤ randomDelay M x ∧ randomDelay M x ≤ M := by sorry
