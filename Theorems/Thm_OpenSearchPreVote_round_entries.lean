import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.round_entries {V : Type} (es : ElectionStrategy)
    (Delivered : DiscoveryNode → PreVoteResponse → Prop) (r : PreVotingRound V)
    (hr : RoundReachable es Delivered r) :
    (∀ p ∈ r.preVotesReceived, NoFresher p.2 r.clusterState ∧ Delivered p.1 p.2) ∧
    (r.preVotesReceived.map Prod.fst).Nodup := by sorry
