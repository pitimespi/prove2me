import Definitions.Def_OpenSearchPreVote

open OpenSearchCoordination OpenSearchPreVote

/-! # Pre-voting and election scheduling -/

/-- A node answers a pre-vote request exactly when it is healthy and knows no leader or knows the requester as its
leader; it then answers with its own current response. -/
theorem OpenSearchPreVote.handlePreVoteRequest_spec (healthy : Bool) (st : CollectorState) (req : PreVoteRequest)
    (resp : PreVoteResponse) :
    handlePreVoteRequest healthy st req = .ok resp ↔
      healthy = true ∧ (st.leader = none ∨ st.leader = some req.sourceNode) ∧ resp = st.response := by
  sorry

/-- The votes a round counts are exactly the ids of the cluster-manager-eligible senders it has recorded. -/
theorem OpenSearchPreVote.votes_mem {V : Type} (r : PreVotingRound V) (x : NodeId) :
    x ∈ r.votes.nodes ↔ ∃ p ∈ r.preVotesReceived, p.1.id = x ∧ p.1.isClusterManagerNode = true := by
  sorry

/-- A round only records responses that are no fresher than the accepted state it started from, only responses
allowed by the delivery predicate, and at most one per sender. -/
theorem OpenSearchPreVote.round_entries {V : Type} (es : ElectionStrategy)
    (Delivered : DiscoveryNode → PreVoteResponse → Prop) (r : PreVotingRound V)
    (hr : RoundReachable es Delivered r) :
    (∀ p ∈ r.preVotesReceived, NoFresher p.2 r.clusterState ∧ Delivered p.1 p.2) ∧
    (r.preVotesReceived.map Prod.fst).Nodup := by
  sorry

/-- A round starts an election only once, only while open, and only when the votes it has recorded, including the
new one, form an election quorum of the last committed and last accepted configurations of the state it started from. -/
theorem OpenSearchPreVote.round_start_quorum {V : Type} (es : ElectionStrategy) (lr resp : PreVoteResponse)
    (sender : DiscoveryNode) (r r' : PreVotingRound V) (m : Option Nat)
    (h : r.handlePreVoteResponse es lr resp sender = (r', true, m)) :
    r.isClosed = false ∧ r.electionStarted = false ∧ r'.electionStarted = true ∧ NoFresher resp r.clusterState ∧
    r'.clusterState = r.clusterState ∧ r'.localNode = r.localNode ∧
    isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion
      r.clusterState.lastCommittedConfiguration r.clusterState.lastAcceptedConfiguration r'.votes = true := by
  sorry

/-- Once a round has started an election, or once it is closed, it never starts one again. -/
theorem OpenSearchPreVote.round_starts_once {V : Type} (es : ElectionStrategy) (lr resp : PreVoteResponse)
    (sender : DiscoveryNode) (r : PreVotingRound V) (h : r.electionStarted = true ∨ r.isClosed = true) :
    (r.handlePreVoteResponse es lr resp sender).2.1 = false ∧
    ((r.handlePreVoteResponse es lr resp sender).1.electionStarted = true ∨
      (r.handlePreVoteResponse es lr resp sender).1.isClosed = true) := by
  sorry

/-- **Pre-voting protects a stable leader.** Suppose a quorum `L` of the last committed or of the last accepted
configuration of node `c`'s accepted state consists of nodes that are unhealthy or follow a leader other than `c`.
Then no pre-voting round of `c` over that state ever starts an election, whatever responses it receives and in whatever
order: every response it can record comes from a node that answered `c`'s request, such nodes are outside `L`, and a
set disjoint from a quorum is not a quorum. A node cut off from a cluster whose majority follows a leader cannot
disrupt it by starting elections when it reconnects. -/
theorem OpenSearchPreVote.no_disruption {V : Type} (es : ElectionStrategy) (healthy : DiscoveryNode → Bool)
    (st : DiscoveryNode → CollectorState) (c : DiscoveryNode) (t : Nat) (s : ClusterState V) (L : List NodeId)
    (hL : s.lastCommittedConfiguration.hasQuorum L = true ∨ s.lastAcceptedConfiguration.hasQuorum L = true)
    (hfollow : ∀ n : DiscoveryNode, n.id ∈ L → healthy n = false ∨ ∃ l, (st n).leader = some l ∧ l ≠ c)
    (r : PreVotingRound V)
    (hr : RoundReachable es (fun n resp => handlePreVoteRequest (healthy n) (st n) ⟨c, t⟩ = .ok resp) r)
    (hs : r.clusterState = s) :
    r.electionStarted = false ∧
    ∀ lr resp sender, handlePreVoteRequest (healthy sender) (st sender) ⟨c, t⟩ = .ok resp →
      (r.handlePreVoteResponse es lr resp sender).2.1 = false := by
  sorry

/-- **A successful pre-vote predicts a successful election.** Let node `c` (with the default election strategy) run a
pre-voting round over its accepted state, every recorded response being the current response of its sender's
coordination state (the senders have not changed state since answering), and let the round start an election. Let `T`
be the election's term: one above `c`'s current term and every term `c` has seen, including the terms in the
responses. Then `c` and every recorded sender accept the `StartJoinRequest` of `c` for `T`, and `c`, handling the
resulting joins in any order — interleaved with any other joins, accepted or not — wins the election. -/
theorem OpenSearchPreVote.preVote_then_election {V : Type} (csc : CoordinationState V)
    (node : DiscoveryNode → CoordinationState V) (r : PreVotingRound V)
    (hr : RoundReachable ElectionStrategy.DEFAULT_INSTANCE
      (fun n resp => (node n).localNode = n ∧ preVoteResponseOf (node n) = resp) r)
    (hstate : r.clusterState = csc.lastAcceptedState) (hlocal : r.localNode = csc.localNode)
    (hstarted : r.electionStarted = true) (maxTermSeen : Nat)
    (hseen : ∀ p ∈ r.preVotesReceived, p.2.currentTerm ≤ maxTermSeen)
    (csc₁ : CoordinationState V) (j₀ : Join)
    (hsj : csc.handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (csc₁, j₀))
    (js : List Join) :
    (∀ p ∈ r.preVotesReceived, ∃ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j)) ∧
    ((∀ p ∈ r.preVotesReceived, ∀ cs' j,
      (node p.1).handleStartJoin ⟨csc.localNode, startElectionTerm csc.currentTerm maxTermSeen⟩ = .ok (cs', j) →
        j ∈ js) →
      (handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).electionWon = true) := by
  sorry

/-! ## Election scheduling -/

/-- Every attempt's delay lies between one millisecond and the attempt's bound, after the grace period. -/
theorem OpenSearchPreVote.attemptDelay_bounds (s : SchedulerSettings) (hs : s.Valid) (k : Nat) (r : Int)
    (g : Nat) :
    1 ≤ maxDelay s k ∧ g + 1 ≤ attemptDelay s k r g ∧ attemptDelay s k r g ≤ g + maxDelay s k := by
  sorry

/-- The bound grows with the attempt number, from the initial timeout, by the back-off time per attempt, until it
reaches the maximum timeout, where it stays. -/
theorem OpenSearchPreVote.maxDelay_schedule (s : SchedulerSettings) (hs : s.Valid) :
    maxDelay s 0 = s.initialTimeout ∧ (∀ k k', k ≤ k' → maxDelay s k ≤ maxDelay s k') ∧
    (∀ k, maxDelay s k < s.maxTimeout → maxDelay s (k + 1) = maxDelay s k + s.backoffTime ∨
      maxDelay s (k + 1) = s.maxTimeout) ∧
    ∀ k, s.maxTimeout ≤ k → maxDelay s k = s.maxTimeout := by
  sorry

/-- `nonNegative` maps the Java `long`s exactly two-to-one onto `[0, 2^63)`: the value `v > 0` comes from `v` and `-v`,
the value `0` from `0` and `Long.MIN_VALUE`. With a uniformly random `long`, `nonNegative` is uniform on `[0, 2^63)`. -/
theorem OpenSearchPreVote.nonNegative_two_to_one (v : Nat) (hv : v < 2 ^ 63) (n : Int)
    (hn : -2 ^ 63 ≤ n ∧ n < 2 ^ 63) :
    nonNegative n = v ↔ n = v ∨ n = (if v = 0 then -2 ^ 63 else -(v : Int)) := by
  sorry
