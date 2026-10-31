import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.default_example :
    contestedBound 3 100 10000 < 6 / 100 ∧ contestedBound 3 100 10000 ^ 5 < 1 / 1000000 := by sorry
