import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.votes_mem {V : Type} (r : PreVotingRound V) (x : NodeId) :
    x ∈ r.votes.nodes ↔ ∃ p ∈ r.preVotesReceived, p.1.id = x ∧ p.1.isClusterManagerNode = true := by sorry
