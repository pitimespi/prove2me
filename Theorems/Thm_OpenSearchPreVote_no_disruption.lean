import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.no_disruption {V : Type} (es : ElectionStrategy) (healthy : DiscoveryNode → Bool)
    (st : DiscoveryNode → CollectorState) (c : DiscoveryNode) (t : Nat) (s : ClusterState V) (L : List NodeId)
    (hL : s.lastCommittedConfiguration.hasQuorum L = true ∨ s.lastAcceptedConfiguration.hasQuorum L = true)
    (hfollow : ∀ n : DiscoveryNode, n.id ∈ L → healthy n = false ∨ ∃ l, (st n).leader = some l ∧ l ≠ c)
    (r : PreVotingRound V)
    (hr : RoundReachable es (fun n resp => handlePreVoteRequest (healthy n) (st n) ⟨c, t⟩ = .ok resp) r)
    (hs : r.clusterState = s) :
    r.electionStarted = false ∧
    ∀ lr resp sender, handlePreVoteRequest (healthy sender) (st sender) ⟨c, t⟩ = .ok resp →
      (r.handlePreVoteResponse es lr resp sender).2.1 = false := by sorry
