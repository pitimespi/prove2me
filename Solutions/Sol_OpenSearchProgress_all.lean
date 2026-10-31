import Definitions.Def_OpenSearchProgress

open OpenSearchCoordination OpenSearchSafety OpenSearchProgress

/-! # Progress under stability -/

/-- **Votes keep counting during a stable election.** Let `c` be a cluster-manager-eligible node of a reachable cluster,
`t` a term above the current terms of `c` and of the voters `Q` (cluster-manager-eligible nodes whose last accepted
state is no fresher than `c`'s, compared as `handleJoin` does). In every stable election execution, once `c` is in
term `t`, `c` accepts the join for `t` of every voter, whenever it arrives, and counts the vote. -/
theorem OpenSearchProgress.election_vote_accepted {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hterm : ∀ q, q = c ∨ q ∈ Q → (W.node q).currentTerm < t)
    (hfresh : ∀ q ∈ Q, (W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion))
    (hconf : (W.node c).lastAcceptedConfiguration.isEmpty = false)
    (W' : Cluster V)
    (hE : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W')
    (hct : (W'.node c).currentTerm = t) (j : Join) (hj : W'.sent (.join j)) (hsrc : j.sourceNode.id ∈ Q)
    (htgt : j.targetNode.id = c) (hjt : j.term = t) :
    ∃ cs' b, (W'.node c).handleJoin P.strategy j = .ok (cs', b) ∧ j.sourceNode.id ∈ cs'.joinVotes.nodes := by
  sorry

/-- **A stable election is won once the votes are in.** Under the same hypotheses, with `Q` an election quorum of `c`'s
last committed and last accepted configurations: in every stable election execution, as soon as `c` is in term `t` and
has counted the votes of all of `Q`, it has won the election. -/
theorem OpenSearchProgress.election_won {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q, q = c ∨ q ∈ Q → (W.node q).currentTerm < t)
    (W' : Cluster V)
    (hE : ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W')
    (hct : (W'.node c).currentTerm = t) (hvotes : ∀ q ∈ Q, q ∈ (W'.node c).joinVotes.nodes) :
    (W'.node c).electionWon = true := by
  sorry

/-- **Stable elections succeed.** Under the hypotheses of `election_vote_accepted` and `election_won`, there is a
stable election execution — `c` and each voter accept `c`'s start-join request for `t`, and `c` counts the voters'
joins — at the end of which `c` has won the election of term `t`. -/
theorem OpenSearchProgress.election_possible {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hc : P.eligible c = true) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q, q = c ∨ q ∈ Q → (W.node q).currentTerm < t)
    (hfresh : ∀ q ∈ Q, (W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm ∨
      ((W.node q).lastAcceptedTerm = (W.node c).lastAcceptedTerm ∧
        (W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion)) :
    ∃ W', ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W' ∧
      (W'.node c).currentTerm = t ∧ (W'.node c).electionWon = true := by
  sorry

/-- **Acknowledgements keep counting during a stable publication.** Let the cluster-manager `c` of term `t` (elected,
in term `t`) have published the state `s` of version `v = lastPublishedVersion`. In every stable publication
execution, while `c` has not published again, every node of `Q` whose current term is `t` either has already
acknowledged `(t, v)` or accepts the publication now; and `c` accepts every acknowledgement of `(t, v)` from a node of
`Q`, whenever it arrives, and counts it. -/
theorem OpenSearchProgress.publication_acks_accepted {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (W' : Cluster V) (hE : PublicationExec P c t Q W W') :
    (∀ q ∈ Q, (W'.node q).currentTerm = t →
      W'.sent (.publishResponse q c ⟨t, s.version⟩) ∨
      ∃ cs' r, (W'.node q).handlePublishRequest ⟨s⟩ = .ok (cs', r)) ∧
    (∀ q ∈ Q, W'.sent (.publishResponse q c ⟨t, s.version⟩) →
      ∃ cs' o, (W'.node c).handlePublishResponse (P.dn q) ⟨t, s.version⟩ = .ok (cs', o) ∧
        q ∈ cs'.publishVotes.nodes) := by
  sorry

/-- **A stable publication is committed once acknowledged by a quorum.** If moreover `Q` is a quorum of `c`'s last
committed and last accepted configurations and of the published state's two configurations, and `c` has counted no
acknowledgement yet (as right after `handleClientValue`), then in every stable publication execution, as soon as `c` has
counted the acknowledgements of all of `Q`, the publication `(t, v)` is committed. (`Q` must be a
quorum of every committed configuration `c` may use when counting: its own, and the published state's.) -/
theorem OpenSearchProgress.publication_committed {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧ s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hpv : (W.node c).publishVotes.nodes = [])
    (W' : Cluster V) (hE : PublicationExec P c t Q W W') (hacks : ∀ q ∈ Q, q ∈ (W'.node c).publishVotes.nodes) :
    Committed W' t s.version := by
  sorry

/-- **Stable publications are committed.** Under the hypotheses of `publication_committed`, with the nodes of `Q` in
terms at most `t`, there is a stable publication execution — each node of `Q` moves to term `t` if needed, accepts the
publication and acknowledges it, and `c` counts the acknowledgements — at the end of which the publication is
committed. -/
theorem OpenSearchProgress.publication_possible {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (c : NodeId) (t : Nat) (Q : List NodeId) (hQ : ∀ q ∈ Q, P.eligible q = true)
    (hwon : (W.node c).electionWon = true) (hct : (W.node c).currentTerm = t)
    (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest c s pt pv)) (hst : s.term = t)
    (hsv : s.version = (W.node c).lastPublishedVersion)
    (hquorum : (W.node c).lastCommittedConfiguration.hasQuorum Q = true ∧
      (W.node c).lastAcceptedConfiguration.hasQuorum Q = true ∧
      s.lastCommittedConfiguration.hasQuorum Q = true ∧ s.lastAcceptedConfiguration.hasQuorum Q = true)
    (hterm : ∀ q ∈ Q, (W.node q).currentTerm ≤ t) :
    ∃ W', PublicationExec P c t Q W W' ∧ Committed W' t s.version := by
  sorry
