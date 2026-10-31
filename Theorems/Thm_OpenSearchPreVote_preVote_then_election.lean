import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.preVote_then_election {V : Type} (csc : CoordinationState V)
    (node : DiscoveryNode → CoordinationState V) (r : PreVotingRound V)
    (hr : RoundReachable ElectionStrategy.DEFAULT_INSTANCE
      (fun n resp => (node n).localNode = n ∧ preVoteResponseOf (node n) = resp) r)
    (hstate : r.clusterState = csc.lastAcceptedState) (hlocal : r.localNode = csc.localNode)
    (hstarted : r.electionStarted = true) (maxTermSeen : Nat)
    (hseen : ∀ p ∈ r.preVotesReceived, p.2.currentTerm ≤ maxTermSeen)
    (csc₁ : CoordinationState V) (j₀ : Join)
    (hsj : csc.handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (csc₁, j₀))
    (js : List Join) (hjs : ∀ j ∈ js, j.term ≤ startElectionTerm csc.currentTerm maxTermSeen) :
    (∀ p ∈ r.preVotesReceived, ∃ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j)) ∧
    ((∀ p ∈ r.preVotesReceived, ∀ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j) →
        j ∈ js) →
      (handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).electionWon = true) := by sorry
