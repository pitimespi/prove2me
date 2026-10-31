import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.round_starts_once {V : Type} (es : ElectionStrategy) (lr resp : PreVoteResponse)
    (sender : DiscoveryNode) (r : PreVotingRound V) (h : r.electionStarted = true ∨ r.isClosed = true) :
    (r.handlePreVoteResponse es lr resp sender).2.1 = false ∧
    ((r.handlePreVoteResponse es lr resp sender).1.electionStarted = true ∨
      (r.handlePreVoteResponse es lr resp sender).1.isClosed = true) := by sorry
