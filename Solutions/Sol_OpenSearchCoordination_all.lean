import Definitions.Def_OpenSearchCoordination

open OpenSearchCoordination

/-! # OpenSearch `CoordinationState`: per-node properties

Statements about the per-node consensus state machine. The cluster-level safety theorems are in the next mission. -/

namespace OpenSearchCoordination

variable {V : Type}

/-! ## Quorums -/

/-- Two quorums of the same voting configuration share a member of the configuration. -/
theorem quorum_intersect (c : VotingConfiguration) (a b : List NodeId)
    (ha : c.hasQuorum a = true) (hb : c.hasQuorum b = true) :
    ∃ x, x ∈ c.nodeIds ∧ x ∈ a ∧ x ∈ b := by
  sorry

/-- A superset of a quorum is a quorum. -/
theorem quorum_mono (c : VotingConfiguration) (a b : List NodeId) (hab : ∀ x, x ∈ a → x ∈ b)
    (ha : c.hasQuorum a = true) : c.hasQuorum b = true := by
  sorry

/-- The empty configuration has no quorum; a node whose configurations are empty can never win an election. -/
theorem empty_no_quorum (a : List NodeId) : VotingConfiguration.EMPTY_CONFIG.hasQuorum a = false := by
  sorry

/-- An empty vote collection is a quorum of no configuration. -/
theorem no_votes_no_quorum (c : VotingConfiguration) : VoteCollection.empty.isQuorum c = false := by
  sorry

/-- Votes are only ever counted from cluster-manager-eligible nodes. -/
theorem addVote_eligible (v : VoteCollection) (n : DiscoveryNode) (x : NodeId) :
    x ∈ (v.addVote n).1.nodes ↔ x ∈ v.nodes ∨ (x = n.id ∧ n.isClusterManagerNode = true) := by
  sorry

/-! ## Terms and accepted states only move forward -/

/-- `handleStartJoin` succeeds exactly when the requested term is greater than the current term; it moves the node to
that term, discards the election and publication state, and votes for the requester with the node's last accepted
term and version (or metadata version, for a term-0 state). The accepted state is unchanged. -/
theorem handleStartJoin_spec (cs : CoordinationState V) (req : StartJoinRequest) (cs' : CoordinationState V)
    (j : Join) :
    cs.handleStartJoin req = .ok (cs', j) ↔
      cs.currentTerm < req.term ∧ cs'.currentTerm = req.term ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
      cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = true ∧ cs'.electionWon = false ∧
      cs'.joinVotes = VoteCollection.empty ∧ cs'.publishVotes = VoteCollection.empty ∧
      cs'.lastPublishedVersion = 0 ∧ cs'.lastPublishedConfiguration = cs.lastAcceptedConfiguration ∧
      j = ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩ := by
  sorry

/-- `handlePublishRequest` accepts only a state of the current term, and (outside the Zen1 compatibility branch, which
needs a term-0 state) only one that is strictly newer than the last accepted state in the lexicographic
(term, version) order. The response names exactly the accepted state's term and version. -/
theorem handlePublishRequest_spec (cs : CoordinationState V) (req : PublishRequest V) (cs' : CoordinationState V)
    (resp : PublishResponse) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handlePublishRequest req = .ok (cs', resp)) :
    cs'.lastAcceptedState = req.acceptedState ∧ req.acceptedState.term = cs.currentTerm ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.localNode = cs.localNode ∧
    resp = ⟨req.acceptedState.term, req.acceptedState.version⟩ ∧
    (cs.lastAcceptedTerm < req.acceptedState.term ∨
      (cs.lastAcceptedTerm = req.acceptedState.term ∧ cs.lastAcceptedVersion < req.acceptedState.version) ∨
      req.acceptedState.term = ZEN1_BWC_TERM) ∧
    cs'.joinVotes = cs.joinVotes ∧ cs'.electionWon = cs.electionWon ∧
    cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    cs'.lastPublishedVersion = cs.lastPublishedVersion ∧
    cs'.lastPublishedConfiguration = cs.lastPublishedConfiguration ∧ cs'.publishVotes = cs.publishVotes := by
  sorry

/-- `handleCommit` changes nothing but the last accepted state's committed configuration (which becomes the accepted
one, the assertion of CS:573) and its cluster-UUID flag; it applies only to the last accepted state, and only in the
current term. -/
theorem handleCommit_spec (cs : CoordinationState V) (c : ApplyCommitRequest) (cs' : CoordinationState V)
    (h : cs.handleCommit c = .ok cs') :
    c.term = cs.currentTerm ∧ c.term = cs.lastAcceptedTerm ∧ c.version = cs.lastAcceptedVersion ∧
    cs' = { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted } ∧
    cs'.lastCommittedConfiguration = cs'.lastAcceptedConfiguration ∧
    cs'.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∧
    cs'.lastAcceptedTerm = cs.lastAcceptedTerm ∧ cs'.lastAcceptedVersion = cs.lastAcceptedVersion ∧
    cs'.lastAcceptedState.value = cs.lastAcceptedState.value := by
  sorry

/-- No handler decreases the current term, and only `handleStartJoin` changes it. The last accepted term never exceeds
the current term, and every handler preserves this. -/
theorem lastAcceptedTerm_le_currentTerm (es : ElectionStrategy) (cs : CoordinationState V)
    (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm) :
    (∀ s cs', cs.setInitialState s = .ok cs' → s.term = 0 → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ r cs' j, cs.handleStartJoin r = .ok (cs', j) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs.currentTerm < cs'.currentTerm) ∧
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ p cs' r, cs.handlePublishRequest p = .ok (cs', r) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ c cs', cs.handleCommit c = .ok cs' → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) := by
  sorry

/-! ## Elections -/

/-- A node only counts the vote of a voter whose last accepted state is no fresher than its own: `handleJoin` succeeds
only if the join is for the current term, the node has started a join since its last reboot, it has been bootstrapped,
and the voter's (accepted term, version) is lexicographically at most the node's (accepted term, version-or-metadata
version). After a successful join, `electionWon` is exactly whether the votes form an election quorum. -/
theorem handleJoin_spec (es : ElectionStrategy) (cs : CoordinationState V) (j : Join) (cs' : CoordinationState V)
    (b : Bool) (h : cs.handleJoin es j = .ok (cs', b)) :
    j.term = cs.currentTerm ∧ cs.startedJoinSinceLastReboot = true ∧
    cs.lastAcceptedConfiguration.isEmpty = false ∧
    (j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion)) ∧
    cs'.joinVotes = (cs.joinVotes.addVote j.sourceNode).1 ∧ b = (cs.joinVotes.addVote j.sourceNode).2 ∧
    cs'.electionWon = cs.isElectionQuorum es cs'.joinVotes ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
    cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    cs'.publishVotes = cs.publishVotes ∧ cs'.lastPublishedConfiguration = cs.lastPublishedConfiguration ∧
    cs'.lastPublishedVersion =
      (if cs'.electionWon = true ∧ cs.electionWon = false then cs.lastAcceptedVersion else cs.lastPublishedVersion) := by
  sorry

theorem default_monotone : ElectionStrategy.DEFAULT_INSTANCE.Monotone := by
  sorry

/-- "We cannot go from won to not won" (the assertion of CS:323-324): for a monotone election strategy, if `electionWon`
agrees with the election quorum before a join (the second clause of `invariant()`), a won election stays won. -/
theorem handleJoin_stays_won (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V) (j : Join)
    (cs' : CoordinationState V) (b : Bool) (hinv : cs.electionWon = cs.isElectionQuorum es cs.joinVotes)
    (h : cs.handleJoin es j = .ok (cs', b)) (hw : cs.electionWon = true) : cs'.electionWon = true := by
  sorry

/-! ## Publication -/

/-- `handleClientValue` publishes only as an elected leader that has accepted its own last publication, only in its
current term, only with a version above the last published one, only with the current committed configuration
(the caller's contract), only reconfiguring when the last accepted configuration is committed, and only to a
configuration in which its join votes are a quorum. -/
theorem handleClientValue_spec (cs : CoordinationState V) (s : ClusterState V) (cs' : CoordinationState V)
    (p : PublishRequest V) (h : cs.handleClientValue s = .ok (cs', p)) :
    cs.electionWon = true ∧ cs.lastPublishedVersion = cs.lastAcceptedVersion ∧ s.term = cs.currentTerm ∧
    cs.lastAcceptedVersion < s.version ∧
    (s.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∨
      cs.lastCommittedConfiguration = cs.lastAcceptedConfiguration) ∧
    cs.joinVotes.isQuorum s.lastAcceptedConfiguration = true ∧
    p = ⟨s⟩ ∧ cs' = { cs with lastPublishedVersion := s.version,
                               lastPublishedConfiguration := s.lastAcceptedConfiguration,
                               publishVotes := VoteCollection.empty } := by
  sorry

/-- `handlePublishResponse` returns a commit only when the publish votes, including the new one, are a quorum of both
the last committed configuration (read now) and the configuration being published; the commit is for the current term
and the version being published, and is sent by this node. -/
theorem handlePublishResponse_spec (cs : CoordinationState V) (src : DiscoveryNode) (r : PublishResponse)
    (cs' : CoordinationState V) (o : Option ApplyCommitRequest) (h : cs.handlePublishResponse src r = .ok (cs', o)) :
    cs.electionWon = true ∧ r.term = cs.currentTerm ∧ r.version = cs.lastPublishedVersion ∧
    cs' = { cs with publishVotes := (cs.publishVotes.addVote src).1 } ∧
    (∀ c, o = some c →
      c = ⟨cs.localNode, cs.currentTerm, cs.lastPublishedVersion⟩ ∧
      cs'.publishVotes.isQuorum cs.lastCommittedConfiguration = true ∧
      cs'.publishVotes.isQuorum cs.lastPublishedConfiguration = true) := by
  sorry

/-! ## The assertions of `invariant()` -/

/-- A freshly constructed (restarted) node satisfies `invariant()` whenever its persisted accepted term is at most its
persisted current term. -/
theorem init_javaInvariant (es : ElectionStrategy) (n : DiscoveryNode) (t : Nat) (s : ClusterState V)
    (h : s.term ≤ t) : (CoordinationState.init n t s).javaInvariant es := by
  sorry

/-- `handleStartJoin` re-establishes `invariant()` from any state whose accepted term is at most its current term. -/
theorem handleStartJoin_javaInvariant (es : ElectionStrategy) (cs : CoordinationState V) (r : StartJoinRequest)
    (cs' : CoordinationState V) (j : Join) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handleStartJoin r = .ok (cs', j)) : cs'.javaInvariant es := by
  sorry

/-- `invariant()` is preserved by `handleJoin` (monotone strategy), `handleClientValue` and `handlePublishResponse`. -/
theorem javaInvariant_preserved (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V)
    (hinv : cs.javaInvariant es) :
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.javaInvariant es) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.javaInvariant es) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.javaInvariant es) := by
  sorry

/-- ... but not by `handlePublishRequest` in isolation: a node can satisfy `invariant()`, accept a publication, and
violate it (its join votes become an election quorum of the new configurations without `electionWon` being set). That
`invariant()` nevertheless holds at every node of every execution is a property of the cluster (next mission). -/
theorem javaInvariant_not_local :
    ∃ (cs : CoordinationState Unit) (p : PublishRequest Unit) (cs' : CoordinationState Unit) (r : PublishResponse),
      cs.javaInvariant ElectionStrategy.DEFAULT_INSTANCE ∧ cs.handlePublishRequest p = .ok (cs', r) ∧
      ¬ cs'.javaInvariant ElectionStrategy.DEFAULT_INSTANCE := by
  sorry

end OpenSearchCoordination
