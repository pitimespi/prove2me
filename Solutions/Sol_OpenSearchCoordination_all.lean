import Definitions.Def_OpenSearchCoordination

open OpenSearchCoordination

/-! # OpenSearch `CoordinationState`: per-node properties

Statements about the per-node consensus state machine. The cluster-level safety theorems are in the next mission. -/



/-! ## Quorums -/

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- Two quorums of the same voting configuration share a member of the configuration. -/
theorem OpenSearchCoordination.quorum_intersect (c : VotingConfiguration) (a b : List NodeId)
    (ha : c.hasQuorum a = true) (hb : c.hasQuorum b = true) :
    ∃ x, x ∈ c.nodeIds ∧ x ∈ a ∧ x ∈ b := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha hb
  have key := filter_length_add_le c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
  have hpos : 0 < (c.nodeIds.filter (fun x => a.contains x && b.contains x)).length := by omega
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at hx
  exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

/-- Filtering by a weaker predicate keeps at least as many elements. -/
private theorem filter_length_mono {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> try omega
    have := h y hp
    rw [hq] at this
    exact absurd this (by decide)

/-- A superset of a quorum is a quorum. -/
theorem OpenSearchCoordination.quorum_mono (c : VotingConfiguration) (a b : List NodeId) (hab : ∀ x, x ∈ a → x ∈ b)
    (ha : c.hasQuorum a = true) : c.hasQuorum b = true := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha ⊢
  have := filter_length_mono c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
    (fun x hx => by rw [List.contains_iff_mem] at hx ⊢; exact hab x hx)
  omega

/-- The empty configuration has no quorum; a node whose configurations are empty can never win an election. -/
theorem OpenSearchCoordination.empty_no_quorum (a : List NodeId) : VotingConfiguration.EMPTY_CONFIG.hasQuorum a = false := by
  rfl

/-- An empty vote collection is a quorum of no configuration. -/
theorem OpenSearchCoordination.no_votes_no_quorum (c : VotingConfiguration) : VoteCollection.empty.isQuorum c = false := by
  unfold VoteCollection.isQuorum VotingConfiguration.hasQuorum VoteCollection.empty
  dsimp only
  rw [decide_eq_false_iff_not]
  have : (c.nodeIds.filter (fun x => ([] : List NodeId).contains x)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; simp
  omega

/-- Votes are only ever counted from cluster-manager-eligible nodes. -/
theorem OpenSearchCoordination.addVote_eligible (v : VoteCollection) (n : DiscoveryNode) (x : NodeId) :
    x ∈ (v.addVote n).1.nodes ↔ x ∈ v.nodes ∨ (x = n.id ∧ n.isClusterManagerNode = true) := by
  unfold VoteCollection.addVote
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    simp only [List.mem_cons, h.1, and_true]
    exact Or.comm
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      not_and, Classical.not_not] at h
    constructor
    · exact Or.inl
    · rintro (hx | ⟨rfl, hc⟩)
      · exact hx
      · exact h hc

/-! ## Terms and accepted states only move forward -/

/-- `handleStartJoin` succeeds exactly when the requested term is greater than the current term; it moves the node to
that term, discards the election and publication state, and votes for the requester with the node's last accepted
term and version (or metadata version, for a term-0 state). The accepted state is unchanged. -/
theorem OpenSearchCoordination.handleStartJoin_spec {V : Type} (cs : CoordinationState V) (req : StartJoinRequest) (cs' : CoordinationState V)
    (j : Join) :
    cs.handleStartJoin req = .ok (cs', j) ↔
      cs.currentTerm < req.term ∧ cs'.currentTerm = req.term ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
      cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = true ∧ cs'.electionWon = false ∧
      cs'.joinVotes = VoteCollection.empty ∧ cs'.publishVotes = VoteCollection.empty ∧
      cs'.lastPublishedVersion = 0 ∧ cs'.lastPublishedConfiguration = cs.lastAcceptedConfiguration ∧
      j = ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩ := by
  unfold CoordinationState.handleStartJoin
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hlt
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl⟩
    rw [if_neg (show ¬ (req.term ≤ cs.currentTerm) by omega)]
    obtain ⟨ln, ct, las, jv, sj, ew, lpv, lpc, pv⟩ := cs'
    dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
    subst h1 h2 h3 h4 h5 h6 h7 h8 h9
    rfl

/-- `handlePublishRequest` accepts only a state of the current term, and (outside the Zen1 compatibility branch, which
needs a term-0 state) only one that is strictly newer than the last accepted state in the lexicographic
(term, version) order. The response names exactly the accepted state's term and version. -/
theorem OpenSearchCoordination.handlePublishRequest_spec {V : Type} (cs : CoordinationState V) (req : PublishRequest V) (cs' : CoordinationState V)
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
  unfold CoordinationState.handlePublishRequest at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hterm
    have hterm' : req.acceptedState.term = cs.currentTerm := Classical.not_not.mp hterm
    split at h
    · rename_i hle
      split at h
      · rename_i hzen
        split at h
        · cases h
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨rfl, hterm', rfl, rfl, rfl, Or.inr (Or.inr hzen), rfl, rfl, rfl, rfl, rfl, rfl⟩
          · cases h
      · cases h
    · rename_i hnle
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, hterm', rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
      by_cases heq : req.acceptedState.term = cs.lastAcceptedTerm
      · right; left
        refine ⟨heq.symm, ?_⟩
        have := fun hv => hnle ⟨heq, hv⟩
        omega
      · left
        unfold CoordinationState.lastAcceptedTerm at heq hcs ⊢
        omega

/-- `handleCommit` changes nothing but the last accepted state's committed configuration (which becomes the accepted
one, the assertion of CS:572) and its cluster-UUID flag; it applies only to the last accepted state, and only in the
current term. -/
theorem OpenSearchCoordination.handleCommit_spec {V : Type} (cs : CoordinationState V) (c : ApplyCommitRequest) (cs' : CoordinationState V)
    (h : cs.handleCommit c = .ok cs') :
    c.term = cs.currentTerm ∧ c.term = cs.lastAcceptedTerm ∧ c.version = cs.lastAcceptedVersion ∧
    cs' = { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted } ∧
    cs'.lastCommittedConfiguration = cs'.lastAcceptedConfiguration ∧
    cs'.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∧
    cs'.lastAcceptedTerm = cs.lastAcceptedTerm ∧ cs'.lastAcceptedVersion = cs.lastAcceptedVersion ∧
    cs'.lastAcceptedState.value = cs.lastAcceptedState.value := by
  unfold CoordinationState.handleCommit at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2 h3
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨Classical.not_not.mp h1, Classical.not_not.mp h2, Classical.not_not.mp h3, rfl, ?_, ?_, ?_, ?_, ?_⟩
        all_goals
          simp only [CoordinationState.lastCommittedConfiguration, CoordinationState.lastAcceptedConfiguration,
            CoordinationState.lastAcceptedTerm, CoordinationState.lastAcceptedVersion, ClusterState.markCommitted]
          split <;> split <;> simp_all

/-- No handler decreases the current term, and only `handleStartJoin` changes it. The last accepted term never exceeds
the current term, and every handler preserves this. -/
theorem OpenSearchCoordination.lastAcceptedTerm_le_currentTerm {V : Type} (es : ElectionStrategy) (cs : CoordinationState V)
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s cs' h hs
    unfold CoordinationState.setInitialState at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, rfl⟩
      show s.term ≤ cs.currentTerm
      omega
  · intro r cs' j h
    obtain ⟨hlt, h1, h2, -⟩ := (handleStartJoin_spec cs r cs' j).1 h
    unfold CoordinationState.lastAcceptedTerm at hcs ⊢
    rw [h2, h1]
    omega
  · intro j cs' b h
    unfold CoordinationState.handleJoin at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    generalize cs.joinVotes.addVote j.sourceNode = va at h
    obtain ⟨votes, added⟩ := va
    dsimp only at h
    split at h
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hcs, rfl⟩
  · intro s cs' p h
    unfold CoordinationState.handleClientValue at h
    repeat (split at h; · cases h)
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hcs, rfl⟩
  · intro p cs' r h
    obtain ⟨h1, h2, h3, -⟩ := handlePublishRequest_spec cs p cs' r hcs h
    unfold CoordinationState.lastAcceptedTerm
    rw [h1, h3, h2]
    exact ⟨Nat.le_refl _, rfl⟩
  · intro n r cs' o h
    unfold CoordinationState.handlePublishResponse at h
    repeat (split at h; · cases h)
    dsimp only at h
    split at h
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hcs, rfl⟩
  · intro c cs' h
    obtain ⟨-, -, -, -, -, -, h1, -⟩ := handleCommit_spec cs c cs' h
    obtain ⟨-, -, -, rfl, -⟩ := handleCommit_spec cs c cs' h
    rw [h1]
    exact ⟨hcs, rfl⟩

/-! ## Elections -/

/-- A node only counts the vote of a voter whose last accepted state is no fresher than its own: `handleJoin` succeeds
only if the join is for the current term, the node has started a join since its last reboot, it has been bootstrapped,
and the voter's (accepted term, version) is lexicographically at most the node's (accepted term, version-or-metadata
version). After a successful join, `electionWon` is exactly whether the votes form an election quorum. -/
theorem OpenSearchCoordination.handleJoin_spec {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join) (cs' : CoordinationState V)
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
  unfold CoordinationState.handleJoin at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  split at h
  · cases h
  rename_i h4
  split at h
  · cases h
  rename_i h5
  have hlex : j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion) := by
    by_cases ht : j.lastAcceptedTerm = cs.lastAcceptedTerm
    · exact Or.inr ⟨ht, by have := fun hv => h4 ⟨ht, hv⟩; omega⟩
    · exact Or.inl (by omega)
  have h1' : j.term = cs.currentTerm := Classical.not_not.mp h1
  have h2' : cs.startedJoinSinceLastReboot = true := by simpa using h2
  have h5' : cs.lastAcceptedConfiguration.isEmpty = false := by simpa using h5
  generalize hva : cs.joinVotes.addVote j.sourceNode = va at h
  obtain ⟨votes, added⟩ := va
  dsimp only at h
  split at h
  · rename_i hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact ⟨h1', h2', h5', hlex, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hw]⟩
  · rename_i hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    exact ⟨h1', h2', h5', hlex, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [hw]⟩

theorem OpenSearchCoordination.default_monotone : ElectionStrategy.DEFAULT_INSTANCE.Monotone := by
  intro _ _ _ _ _ _ _ _ _ _
  rfl

/-- "We cannot go from won to not won" (the assertion of CS:323-324): for a monotone election strategy, if `electionWon`
agrees with the election quorum before a join (the second clause of `invariant()`), a won election stays won. -/
theorem OpenSearchCoordination.handleJoin_stays_won {V : Type} (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V) (j : Join)
    (cs' : CoordinationState V) (b : Bool) (hinv : cs.electionWon = cs.isElectionQuorum es cs.joinVotes)
    (h : cs.handleJoin es j = .ok (cs', b)) (hw : cs.electionWon = true) : cs'.electionWon = true := by
  obtain ⟨-, -, -, -, hj, -, he, -⟩ := handleJoin_spec es cs j cs' b h
  have hsub : ∀ x, x ∈ cs.joinVotes.nodes → x ∈ cs'.joinVotes.nodes := by
    intro x hx
    rw [hj, addVote_eligible]
    exact Or.inl hx
  rw [hw] at hinv
  have hq := hinv.symm
  unfold CoordinationState.isElectionQuorum VoteCollection.isQuorum at hq
  rw [he]
  unfold CoordinationState.isElectionQuorum VoteCollection.isQuorum
  simp only [Bool.and_eq_true] at hq ⊢
  obtain ⟨⟨hc, ha⟩, hs⟩ := hq
  exact ⟨⟨quorum_mono _ _ _ hsub hc, quorum_mono _ _ _ hsub ha⟩, hes _ _ _ _ _ _ _ _ hsub hs⟩

/-! ## Publication -/

/-- `handleClientValue` publishes only as an elected leader that has accepted its own last publication, only in its
current term, only with a version above the last published one, only with the current committed configuration
(the caller's contract), only reconfiguring when the last accepted configuration is committed, and only to a
configuration in which its join votes are a quorum. -/
theorem OpenSearchCoordination.handleClientValue_spec {V : Type} (cs : CoordinationState V) (s : ClusterState V) (cs' : CoordinationState V)
    (p : PublishRequest V) (h : cs.handleClientValue s = .ok (cs', p)) :
    cs.electionWon = true ∧ cs.lastPublishedVersion = cs.lastAcceptedVersion ∧ s.term = cs.currentTerm ∧
    cs.lastAcceptedVersion < s.version ∧
    (s.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∨
      cs.lastCommittedConfiguration = cs.lastAcceptedConfiguration) ∧
    cs.joinVotes.isQuorum s.lastAcceptedConfiguration = true ∧
    p = ⟨s⟩ ∧ cs' = { cs with lastPublishedVersion := s.version,
                               lastPublishedConfiguration := s.lastAcceptedConfiguration,
                               publishVotes := VoteCollection.empty } := by
  unfold CoordinationState.handleClientValue at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  split at h
  · cases h
  rename_i h4
  split at h
  · cases h
  rename_i h5
  split at h
  · cases h
  rename_i h6
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have h2' : cs.lastPublishedVersion = cs.lastAcceptedVersion := Classical.not_not.mp h2
  refine ⟨by simpa using h1, h2', Classical.not_not.mp h3, by omega, ?_, by simpa using h6, rfl, rfl⟩
  by_cases hx : s.lastAcceptedConfiguration = cs.lastAcceptedConfiguration
  · exact Or.inl hx
  · exact Or.inr (Classical.not_not.mp (fun hy => h5 ⟨hx, hy⟩))

/-- `handlePublishResponse` returns a commit only when the publish votes, including the new one, are a quorum of both
the last committed configuration (read now) and the configuration being published; the commit is for the current term
and the version being published, and is sent by this node. -/
theorem OpenSearchCoordination.handlePublishResponse_spec {V : Type} (cs : CoordinationState V) (src : DiscoveryNode) (r : PublishResponse)
    (cs' : CoordinationState V) (o : Option ApplyCommitRequest) (h : cs.handlePublishResponse src r = .ok (cs', o)) :
    cs.electionWon = true ∧ r.term = cs.currentTerm ∧ r.version = cs.lastPublishedVersion ∧
    cs' = { cs with publishVotes := (cs.publishVotes.addVote src).1 } ∧
    (∀ c, o = some c →
      c = ⟨cs.localNode, cs.currentTerm, cs.lastPublishedVersion⟩ ∧
      cs'.publishVotes.isQuorum cs.lastCommittedConfiguration = true ∧
      cs'.publishVotes.isQuorum cs.lastPublishedConfiguration = true) := by
  unfold CoordinationState.handlePublishResponse at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  have h1' : cs.electionWon = true := by simpa using h1
  have h2' : r.term = cs.currentTerm := Classical.not_not.mp h2
  have h3' : r.version = cs.lastPublishedVersion := Classical.not_not.mp h3
  dsimp only at h
  split at h
  · rename_i hq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨h1', h2', h3', rfl, ?_⟩
    intro c hc
    cases hc
    unfold CoordinationState.isPublishQuorum at hq
    rw [Bool.and_eq_true] at hq
    exact ⟨by rw [h2', h3'], hq.1, hq.2⟩
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨h1', h2', h3', rfl, ?_⟩
    intro c hc
    cases hc

/-! ## The assertions of `invariant()` -/

/-- A freshly constructed (restarted) node satisfies `invariant()` whenever its persisted accepted term is at most its
persisted current term. -/
theorem OpenSearchCoordination.init_javaInvariant {V : Type} (es : ElectionStrategy) (n : DiscoveryNode) (t : Nat) (s : ClusterState V)
    (h : s.term ≤ t) : (CoordinationState.init n t s).javaInvariant es := by
  unfold CoordinationState.javaInvariant
  refine ⟨h, ?_, rfl, (fun h => by cases h), Or.inl rfl⟩
  unfold CoordinationState.isElectionQuorum CoordinationState.init
  dsimp only
  rw [no_votes_no_quorum]
  rfl

/-- `handleStartJoin` re-establishes `invariant()` from any state whose accepted term is at most its current term. -/
theorem OpenSearchCoordination.handleStartJoin_javaInvariant {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (r : StartJoinRequest)
    (cs' : CoordinationState V) (j : Join) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handleStartJoin r = .ok (cs', j)) : cs'.javaInvariant es := by
  obtain ⟨hlt, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := (handleStartJoin_spec cs r cs' j).1 h
  unfold CoordinationState.javaInvariant
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold CoordinationState.lastAcceptedTerm at hcs ⊢
    rw [h2, h1]
    omega
  · unfold CoordinationState.isElectionQuorum
    rw [h5, h6, no_votes_no_quorum]
    rfl
  · rw [h5, h8]
    rfl
  · rw [h5]
    intro h
    cases h
  · left
    rw [h7]
    rfl

/-- `invariant()` is preserved by `handleJoin` (monotone strategy), `handleClientValue` and `handlePublishResponse`. -/
theorem OpenSearchCoordination.javaInvariant_preserved {V : Type} (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V)
    (hinv : cs.javaInvariant es) :
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.javaInvariant es) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.javaInvariant es) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.javaInvariant es) := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro j cs' b h
    have hstay := handleJoin_stays_won es hes cs j cs' b i2 h
    obtain ⟨-, hsj, -, -, -, -, he, hct, hlas, hln, hsj', hpv, -, hlpv⟩ := handleJoin_spec es cs j cs' b h
    have hq : cs'.isElectionQuorum es cs'.joinVotes = cs.isElectionQuorum es cs'.joinVotes := by
      unfold CoordinationState.isElectionQuorum CoordinationState.lastCommittedConfiguration
        CoordinationState.lastAcceptedConfiguration CoordinationState.lastAcceptedTerm
        CoordinationState.lastAcceptedVersion
      rw [hct, hlas, hln]
    unfold CoordinationState.javaInvariant
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold CoordinationState.lastAcceptedTerm at i1 ⊢
      rw [hlas, hct]
      exact i1
    · rw [hq]
      exact he
    · have hlav : cs'.lastAcceptedVersion = cs.lastAcceptedVersion := by
        unfold CoordinationState.lastAcceptedVersion
        rw [hlas]
      rw [hlpv, hlav]
      cases hw' : cs'.electionWon <;> cases hw : cs.electionWon <;> simp_all
    · intro _
      rw [hsj']
      exact hsj
    · rw [hpv]
      rcases i5 with i5 | i5
      · exact Or.inl i5
      · exact Or.inr (hstay i5)
  · intro s cs' p h
    obtain ⟨hw, hpv, -, hv, -, -, -, rfl⟩ := handleClientValue_spec cs s cs' p h
    refine ⟨i1, i2, ?_, i4, Or.inl rfl⟩
    show (if cs.electionWon = true then s.version ≥ cs.lastAcceptedVersion else s.version = 0)
    rw [if_pos hw]
    omega
  · intro n r cs' o h
    obtain ⟨hw, -, -, rfl, -⟩ := handlePublishResponse_spec cs n r cs' o h
    exact ⟨i1, i2, i3, i4, Or.inr hw⟩

/-- ... but not by `handlePublishRequest` in isolation: a node can satisfy `invariant()`, accept a publication, and
violate it (its join votes become an election quorum of the new configurations without `electionWon` being set). That
`invariant()` nevertheless holds at every node of every execution is a property of the cluster (next mission). -/
theorem OpenSearchCoordination.javaInvariant_not_local :
    ∃ (cs : CoordinationState Unit) (p : PublishRequest Unit) (cs' : CoordinationState Unit) (r : PublishResponse),
      cs.javaInvariant ElectionStrategy.DEFAULT_INSTANCE ∧ cs.handlePublishRequest p = .ok (cs', r) ∧
      ¬ cs'.javaInvariant ElectionStrategy.DEFAULT_INSTANCE := by
  refine ⟨⟨⟨0, true⟩, 1, ⟨0, 0, 0, ⟨[1, 2, 3], by decide⟩, ⟨[1, 2, 3], by decide⟩, none, false, false, ()⟩,
      ⟨[4]⟩, true, false, 0, ⟨[1, 2, 3], by decide⟩, VoteCollection.empty⟩,
    ⟨⟨1, 1, 0, ⟨[4], by decide⟩, ⟨[4], by decide⟩, none, false, false, ()⟩⟩,
    ⟨⟨0, true⟩, 1, ⟨1, 1, 0, ⟨[4], by decide⟩, ⟨[4], by decide⟩, none, false, false, ()⟩,
      ⟨[4]⟩, true, false, 0, ⟨[1, 2, 3], by decide⟩, VoteCollection.empty⟩,
    ⟨1, 1⟩, ?_, ?_, ?_⟩
  · unfold CoordinationState.javaInvariant
    decide
  · rfl
  · unfold CoordinationState.javaInvariant
    decide

