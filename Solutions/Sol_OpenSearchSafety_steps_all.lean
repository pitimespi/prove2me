import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_descends_trans
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_descends_parent
import Theorems.Thm_OpenSearchSafety_inv_reign_first
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_eligible_of_won
import Theorems.Thm_OpenSearchSafety_inv_won_of_electionWon
import Theorems.Thm_OpenSearchSafety_inv_election_unique

open OpenSearchCoordination OpenSearchSafety

/-! # OpenSearch cluster coordination: the invariant holds initially and is preserved by every step

One public theorem per `Step` constructor, with the constructor's hypotheses, `Inv P W`, `P.InitCompatible` and
the default election strategy, concluding `Inv P W'` for the constructor's successor `W'`. Only `inv_join` (an
election win) needs the static lemmas about elections (`inv_election_unique`, `inv_reign_first`); the other steps are
local.
The private lemmas at the top are shared infrastructure: updating a cluster, monotonicity of every soup-only notion
under sending, quorums, and the handlers' effects in a form that rewrites (`cs' = { cs with … }`). -/

/-! ## Updating a cluster -/

private theorem set_node_self {V : Type} (W : Cluster V) (n : NodeId) (cs : CoordinationState V) :
    (W.set n cs).node n = cs := by
  simp [Cluster.set]

private theorem set_node_ne {V : Type} (W : Cluster V) (n m : NodeId) (cs : CoordinationState V) (h : m ≠ n) :
    (W.set n cs).node m = W.node m := by
  simp [Cluster.set, h]

private theorem set_sent {V : Type} (W : Cluster V) (n : NodeId) (cs : CoordinationState V) :
    (W.set n cs).sent = W.sent := rfl

private theorem send_node {V : Type} (W : Cluster V) (m : Message V) : (W.send m).node = W.node := rfl

private theorem send_sent {V : Type} (W : Cluster V) (m x : Message V) :
    (W.send m).sent x ↔ W.sent x ∨ x = m := Iff.rfl

/-! ## Notions over the soup only grow when messages are sent -/

private theorem committed_mono {V : Type} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m) {t : Nat} {v : Int}
    (h : Committed W t v) : Committed W' t v := by
  obtain ⟨src, h⟩ := h
  exact ⟨src, hg _ h⟩

private theorem published_mono {V : Type} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m) {t : Nat} {v : Int}
    (h : Published W t v) : Published W' t v := by
  obtain ⟨src, s, pt, pv, hs, h1, h2⟩ := h
  exact ⟨src, s, pt, pv, hg _ hs, h1, h2⟩

private theorem parent_mono {V : Type} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m) {t t' : Nat}
    {v v' : Int} (h : Parent W t v t' v') : Parent W' t v t' v' := by
  obtain ⟨src, s, hs, h1, h2⟩ := h
  exact ⟨src, s, hg _ hs, h1, h2⟩

private theorem descends_mono {V : Type} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m) {t t' : Nat}
    {v v' : Int} (h : Descends W t v t' v') : Descends W' t v t' v' := by
  induction h with
  | refl => exact .refl _ _
  | step _ _ _ _ _ hp ih => exact .step _ _ _ _ _ _ ih (parent_mono hg hp)

private theorem realizes_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {t : Nat} {v : Int} {x y : VotingConfiguration} (h : Realizes P W t v x y) : Realizes P W' t v x y := by
  rcases h with h | ⟨src, s, pt, pv, hs, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨src, s, pt, pv, hg _ hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩)⟩

private theorem joinVoters_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {L : NodeId} {t : Nat} {J : List NodeId} (h : JoinVoters P W L t J) : JoinVoters P W' L t J := by
  intro x hx
  obtain ⟨he, j, hj, h1⟩ := h x hx
  exact ⟨he, j, hg _ hj, h1⟩

private theorem baseVoters_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {L : NodeId} {t bt : Nat} {bv : Int} {J : List NodeId} (h : BaseVoters P W L t bt bv J) :
    BaseVoters P W' L t bt bv J := by
  intro x hx
  obtain ⟨he, j, hj, h1⟩ := h x hx
  exact ⟨he, j, hg _ hj, h1⟩

private theorem respVoters_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {t : Nat} {v : Int} {A : List NodeId} (h : RespVoters P W t v A) : RespVoters P W' t v A := by
  intro x hx
  obtain ⟨he, d, hd⟩ := h x hx
  exact ⟨he, d, hg _ hd⟩

private theorem electionRecord_mono {V : Type} {P : Params} {W W' : Cluster V} (hg : ∀ m, W.sent m → W'.sent m)
    {L : NodeId} {t bt : Nat} {bv : Int} {x y : VotingConfiguration} {J : List NodeId}
    (h : ElectionRecord P W L t bt bv x y J) : ElectionRecord P W' L t bt bv x y J := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, realizes_mono hg h2, baseVoters_mono hg h3, h4, h5⟩

/-! ## Quorums and vote collections (as in the per-node mission) -/

private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- Two quorums of the same voting configuration share a member of the configuration. -/
private theorem quorum_intersect (c : VotingConfiguration) (a b : List NodeId)
    (ha : c.hasQuorum a = true) (hb : c.hasQuorum b = true) :
    ∃ x, x ∈ c.nodeIds ∧ x ∈ a ∧ x ∈ b := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha hb
  have key := filter_length_add_le c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
  have hpos : 0 < (c.nodeIds.filter (fun x => a.contains x && b.contains x)).length := by omega
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at hx
  exact ⟨x, hx.1, hx.2.1, hx.2.2⟩

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
private theorem quorum_mono (c : VotingConfiguration) (a b : List NodeId) (hab : ∀ x, x ∈ a → x ∈ b)
    (ha : c.hasQuorum a = true) : c.hasQuorum b = true := by
  simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at ha ⊢
  have := filter_length_mono c.nodeIds (fun x => a.contains x) (fun x => b.contains x)
    (fun x hx => by rw [List.contains_iff_mem] at hx ⊢; exact hab x hx)
  omega

/-- No configuration has a quorum of the empty list. -/
private theorem hasQuorum_nil (c : VotingConfiguration) : c.hasQuorum [] = false := by
  unfold VotingConfiguration.hasQuorum
  rw [decide_eq_false_iff_not]
  have : (c.nodeIds.filter (fun x => ([] : List NodeId).contains x)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; simp
  omega

/-- An empty vote collection is a quorum of no configuration. -/
private theorem isQuorum_empty (c : VotingConfiguration) : VoteCollection.empty.isQuorum c = false :=
  hasQuorum_nil c

/-- The empty configuration has no quorum. -/
private theorem empty_no_quorum (a : List NodeId) : VotingConfiguration.EMPTY_CONFIG.hasQuorum a = false := by
  rfl

/-- A quorum is a nonempty list. -/
private theorem ne_nil_of_hasQuorum (c : VotingConfiguration) (a : List NodeId) (h : c.hasQuorum a = true) :
    a ≠ [] := by
  intro e
  rw [e, hasQuorum_nil] at h
  cases h

/-- Votes are only ever counted from cluster-manager-eligible nodes. -/
private theorem addVote_mem (v : VoteCollection) (n : DiscoveryNode) (x : NodeId) :
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

/-! ## The handlers' effects -/

private theorem spec_setInitialState {V : Type} (cs : CoordinationState V) (s : ClusterState V)
    (cs' : CoordinationState V) (h : cs.setInitialState s = .ok cs') :
    cs.lastAcceptedConfiguration.isEmpty = true ∧ cs' = { cs with lastAcceptedState := s } := by
  unfold CoordinationState.setInitialState at h
  split at h
  · cases h
  · rename_i hne
    simp only [Except.ok.injEq] at h
    exact ⟨by simpa using hne, h.symm⟩

private theorem spec_startJoin {V : Type} (cs : CoordinationState V) (req : StartJoinRequest)
    (cs' : CoordinationState V) (j : Join) (h : cs.handleStartJoin req = .ok (cs', j)) :
    cs.currentTerm < req.term ∧
    cs' = { cs with currentTerm := req.term, lastPublishedVersion := 0,
                    lastPublishedConfiguration := cs.lastAcceptedConfiguration, startedJoinSinceLastReboot := true,
                    electionWon := false, joinVotes := VoteCollection.empty,
                    publishVotes := VoteCollection.empty } ∧
    j = ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩ := by
  unfold CoordinationState.handleStartJoin at h
  split at h
  · cases h
  · rename_i hlt
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, rfl, rfl⟩

private theorem spec_join {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join)
    (cs' : CoordinationState V) (b : Bool) (h : cs.handleJoin es j = .ok (cs', b)) :
    j.term = cs.currentTerm ∧ cs.startedJoinSinceLastReboot = true ∧
    cs.lastAcceptedConfiguration.isEmpty = false ∧
    (j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion)) ∧
    cs' = { cs with joinVotes := (cs.joinVotes.addVote j.sourceNode).1,
                    electionWon := cs.isElectionQuorum es (cs.joinVotes.addVote j.sourceNode).1,
                    lastPublishedVersion :=
                      if cs.isElectionQuorum es (cs.joinVotes.addVote j.sourceNode).1 = true ∧
                          cs.electionWon = false
                      then cs.lastAcceptedVersion else cs.lastPublishedVersion } := by
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
  refine ⟨h1', h2', h5', hlex, ?_⟩
  generalize hva : cs.joinVotes.addVote j.sourceNode = va at h ⊢
  obtain ⟨votes, added⟩ := va
  dsimp only at h ⊢
  split at h
  · rename_i hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    simp [hw]
  · rename_i hw
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    have : ¬ (cs.isElectionQuorum es votes = true ∧ cs.electionWon = false) := hw
    simp only [this, if_false]

private theorem spec_clientValue {V : Type} (cs : CoordinationState V) (s : ClusterState V)
    (cs' : CoordinationState V) (p : PublishRequest V) (h : cs.handleClientValue s = .ok (cs', p)) :
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

private theorem spec_publish {V : Type} (cs : CoordinationState V) (req : PublishRequest V)
    (cs' : CoordinationState V) (resp : PublishResponse) (h : cs.handlePublishRequest req = .ok (cs', resp)) :
    req.acceptedState.term = cs.currentTerm ∧
    (req.acceptedState.term = 0 ∨
      ¬ (req.acceptedState.term = cs.lastAcceptedTerm ∧ req.acceptedState.version ≤ cs.lastAcceptedVersion)) ∧
    resp = ⟨req.acceptedState.term, req.acceptedState.version⟩ ∧
    cs' = { cs with lastAcceptedState := req.acceptedState } := by
  unfold CoordinationState.handlePublishRequest at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hterm
    have hterm' : req.acceptedState.term = cs.currentTerm := Classical.not_not.mp hterm
    split at h
    · split at h
      · rename_i hzen
        split at h
        · cases h
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨hterm', Or.inl hzen, rfl, rfl⟩
          · cases h
      · cases h
    · rename_i hnle
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hterm', Or.inr hnle, rfl, rfl⟩

private theorem spec_respond {V : Type} (cs : CoordinationState V) (src : DiscoveryNode) (r : PublishResponse)
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

private theorem spec_commit {V : Type} (cs : CoordinationState V) (c : ApplyCommitRequest) (cs' : CoordinationState V)
    (h : cs.handleCommit c = .ok cs') :
    c.term = cs.currentTerm ∧ c.term = cs.lastAcceptedTerm ∧ c.version = cs.lastAcceptedVersion ∧
    cs' = { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted } := by
  unfold CoordinationState.handleCommit at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2 h3
        simp only [Except.ok.injEq] at h
        exact ⟨Classical.not_not.mp h1, Classical.not_not.mp h2, Classical.not_not.mp h3, h.symm⟩

/-- `markCommitted` keeps the term, the version and the last accepted configuration, and makes the last committed
configuration the last accepted one. -/
private theorem markCommitted_spec {V : Type} (s : ClusterState V) :
    s.markCommitted.term = s.term ∧ s.markCommitted.version = s.version ∧
    s.markCommitted.lastAcceptedConfiguration = s.lastAcceptedConfiguration ∧
    s.markCommitted.lastCommittedConfiguration = s.lastAcceptedConfiguration := by
  unfold ClusterState.markCommitted
  dsimp only
  split <;> split <;> simp_all

/-- At a term ≥ 1, `versionOrMetadataVersion` is the version. -/
private theorem vomv_of_pos {V : Type} (cs : CoordinationState V) (h : cs.lastAcceptedTerm ≠ 0) :
    cs.lastAcceptedVersionOrMetadataVersion = cs.lastAcceptedVersion := by
  unfold CoordinationState.lastAcceptedVersionOrMetadataVersion ClusterState.versionOrMetadataVersion
  split
  · rename_i hc; exact absurd hc h
  · rfl

/-! ## Initial clusters -/

/-- A fresh cluster satisfies the invariant: no message has been sent, and every node is in term 0 with a
never-bootstrapped accepted state and the constructor's transient state. -/
theorem OpenSearchSafety.inv_init {V : Type} (P : Params) (W : Cluster V) (h : Initial P W) : Inv P W := by
  obtain ⟨hnodes, hsent⟩ := h
  have hew : ∀ n, (W.node n).electionWon = false := by
    intro n; obtain ⟨s, -, -, -, he⟩ := hnodes n; rw [he]; rfl
  have hjv : ∀ n, (W.node n).joinVotes = VoteCollection.empty := by
    intro n; obtain ⟨s, -, -, -, he⟩ := hnodes n; rw [he]; rfl
  have hpv : ∀ n, (W.node n).publishVotes = VoteCollection.empty := by
    intro n; obtain ⟨s, -, -, -, he⟩ := hnodes n; rw [he]; rfl
  have hsj : ∀ n, (W.node n).startedJoinSinceLastReboot = false := by
    intro n; obtain ⟨s, -, -, -, he⟩ := hnodes n; rw [he]; rfl
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := ?_, join_term_le := ?_, join_unique := ?_,
      join_after_response := ?_, response_le := ?_, response_published := ?_,
      pub_wf := ?_, pub_parent := ?_, pub_unique := ?_, pub_rooted := ?_,
      pub_same_term := ?_, pub_voters := ?_, pub_election := ?_,
      commit_quorum := ?_, won_unique := ?_, pub_source_term := ?_, leader_pubs := ?_,
      leader_inflight := ?_, leader_settled := ?_ }
  · intro n; obtain ⟨s, -, -, -, he⟩ := hnodes n; rw [he]; rfl
  · intro n _; obtain ⟨s, -, -, -, he⟩ := hnodes n; rw [he]; exact ⟨rfl, rfl⟩
  · intro n hw; rw [hew n] at hw; cases hw
  · intro n hn; rw [hjv n] at hn; exact absurd rfl hn
  · intro n hs; rw [hsj n] at hs; cases hs
  · intro n hw; rw [hew n] at hw; cases hw
  · intro n _ hq; rw [hjv n, isQuorum_empty] at hq; cases hq.1
  · intro n m hm; rw [hjv n] at hm; cases hm
  · intro n m hm; rw [hpv n] at hm; cases hm
  · intro n _; obtain ⟨s, h0, -, -, he⟩ := hnodes n; rw [he]
    show s.term ≤ 0
    omega
  · intro n _; obtain ⟨s, h0, h1, h2, he⟩ := hnodes n; rw [he]; exact Or.inl ⟨h0, h1, h2⟩
  · intro j hj; exact absurd hj (hsent _)
  · intro j hj; exact absurd hj (hsent _)
  · intro j _ hj; exact absurd hj (hsent _)
  · intro j _ _ _ hj; exact absurd hj (hsent _)
  · intro _ _ _ hr; exact absurd hr (hsent _)
  · intro _ _ _ hr; exact absurd hr (hsent _)
  · intro _ _ _ _ hs; exact absurd hs (hsent _)
  · intro _ _ _ _ hs; exact absurd hs (hsent _)
  · intro _ _ _ _ _ _ _ _ hs; exact absurd hs (hsent _)
  · intro _ _ _ _ hs; exact absurd hs (hsent _)
  · intro _ _ _ _ _ _ _ _ hs; exact absurd hs (hsent _)
  · intro _ _ _ _ hs; exact absurd hs (hsent _)
  · intro _ _ _ _ hs; exact absurd hs (hsent _)
  · intro c hc; exact absurd hc (hsent _)
  · intro a _ _ ⟨_, ha⟩ _
    rcases ha with ⟨hw, -⟩ | ⟨_, _, _, hs, -⟩
    · rw [hew a] at hw; cases hw
    · exact absurd hs (hsent _)
  · intro _ _ _ _ hs; exact absurd hs (hsent _)
  · intro n hw; rw [hew n] at hw; cases hw
  · intro n hw; rw [hew n] at hw; cases hw
  · intro n hw; rw [hew n] at hw; cases hw

/-! ## Steps -/

/-- `bootstrap` preserves the invariant. -/
theorem OpenSearchSafety.inv_bootstrap {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (X : VotingConfiguration) (s : ClusterState V) (cs' : CoordinationState V) (hX : P.initConfs X)
    (hcontract : (W.node n).initialStateContract s)
    (hconf : s.lastCommittedConfiguration = X ∧ s.lastAcceptedConfiguration = X)
    (h : (W.node n).setInitialState s = .ok cs') : Inv P (W.set n cs') := by
  obtain ⟨-, hcs⟩ := spec_setInitialState _ _ _ h
  obtain ⟨hlat, -, -, -, hew, hjv, -, hs0, -, -, -⟩ := hcontract
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = (W.node n).currentTerm := by rw [hcs]
  have e_ew : cs'.electionWon = (W.node n).electionWon := by rw [hcs]
  have e_jv : cs'.joinVotes = (W.node n).joinVotes := by rw [hcs]
  have e_pv : cs'.publishVotes = (W.node n).publishVotes := by rw [hcs]
  have e_sj : cs'.startedJoinSinceLastReboot = (W.node n).startedJoinSinceLastReboot := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = (W.node n).lastPublishedVersion := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = 0 := by rw [hcs]; exact hs0
  have e_lav : cs'.lastAcceptedVersion = s.version := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = X := by rw [hcs]; exact hconf.1
  have e_lac : cs'.lastAcceptedConfiguration = X := by rw [hcs]; exact hconf.2
  have hjv0 : (W.node n).joinVotes.nodes = [] := List.isEmpty_iff.mp hjv
  have hg : ∀ m, W.sent m → (W.set n cs').sent m := fun _ h => h
  -- the bootstrapping node never accepted a publication, so it sent no publish response
  have hnoresp : ∀ d r, W.sent (.publishResponse n d r) → P.eligible n = true → False := by
    intro d r hr hne
    obtain ⟨-, h2⟩ := hinv.response_le n d r hr hne
    obtain ⟨s', pt, pv, hs', hst, -⟩ := hinv.response_published n d r hr
    have := (hinv.pub_wf _ _ _ _ hs').2.1
    unfold KeyLE at h2
    rw [hlat] at h2
    omega
  have hwon : ∀ a t, Won P (W.set n cs') a t → Won P W a t := by
    rintro a t ⟨he, hw | hp⟩
    · by_cases ha : a = n
      · subst ha; rw [set_node_self, e_ew, e_ct] at hw; exact ⟨he, Or.inl hw⟩
      · rw [set_node_ne _ _ _ _ ha] at hw; exact ⟨he, Or.inl hw⟩
    · exact ⟨he, Or.inr hp⟩
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := hinv.join_wf, join_term_le := ?_, join_unique := hinv.join_unique,
      join_after_response := hinv.join_after_response, response_le := ?_,
      response_published := hinv.response_published, pub_wf := hinv.pub_wf, pub_parent := hinv.pub_parent,
      pub_unique := hinv.pub_unique, pub_rooted := ?_, pub_same_term := ?_, pub_voters := hinv.pub_voters,
      pub_election := hinv.pub_election, commit_quorum := hinv.commit_quorum, won_unique := ?_,
      pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_, leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ln]; exact hinv.localNode_eq m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_pv]; exact hinv.idle_of_not_won m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_sj]; exact hinv.won_started m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv, e_sj]; exact hinv.votes_started m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj, e_ct]; exact hinv.started_term_pos m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, hew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv]; intro _ h
      have h1 := h.1
      unfold VoteCollection.isQuorum at h1
      rw [hjv0, hasQuorum_nil] at h1
      cases h1
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv, hjv0]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.joinVotes_sent m x
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_pv, e_ct, e_lpv]; exact hinv.publishVotes_sent m x
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.publishVotes_sent m x
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lat]; exact Nat.zero_le _
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lat, e_lav, e_lcc, e_lac]
      exact Or.inr (Or.inl ⟨rfl, rfl, hX⟩)
    · rw [set_node_ne _ _ _ _ hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j hj hje
    by_cases hm : j.sourceNode.id = n
    · rw [hm, set_node_self, e_ct]; have := hinv.join_term_le j hj hje; rw [hm] at this; exact this
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.join_term_le j hj hje
  · intro a d r hr ha
    by_cases hm : a = n
    · subst hm; exact absurd (hnoresp d r hr ha) id
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.response_le a d r hr ha
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv hs
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' hs hs' ht).imp (descends_mono hg) (descends_mono hg)
  · intro a b t ha hb
    exact hinv.won_unique a b t (hwon a t ha) (hwon b t hb)
  · intro src s pt pv hs
    by_cases hm : src = n
    · subst hm; rw [set_node_self, e_ct, e_ew, e_sj]; exact hinv.pub_source_term src s pt pv hs
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.pub_source_term src s pt pv hs
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, hew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv hs ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, hew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]
      intro hw hne
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne
      exact ⟨s, hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, hew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.leader_settled m

/-- `startJoin` preserves the invariant. -/
theorem OpenSearchSafety.inv_startJoin {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n src : NodeId) (t : Nat) (cs' : CoordinationState V) (j : Join) (hsrc : P.eligible src = true)
    (h : (W.node n).handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)) : Inv P ((W.set n cs').send (.join j)) := by
  obtain ⟨hlt, hcs, hj⟩ := spec_startJoin _ _ _ _ h
  have hlt : (W.node n).currentTerm < t := hlt
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = t := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hcs]; rfl
  have e_lav : cs'.lastAcceptedVersion = (W.node n).lastAcceptedVersion := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := by rw [hcs]; rfl
  have e_lac : cs'.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; rfl
  have e_ew : cs'.electionWon = false := by rw [hcs]
  have e_jv : cs'.joinVotes = VoteCollection.empty := by rw [hcs]
  have e_pv : cs'.publishVotes = VoteCollection.empty := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = 0 := by rw [hcs]
  have j_src : j.sourceNode = P.dn n := by rw [hj, ← hinv.localNode_eq n]
  have j_srcid : j.sourceNode.id = n := by rw [j_src]; rfl
  have j_tgt : j.targetNode = P.dn src := by rw [hj]
  have j_term : j.term = t := by rw [hj]
  have j_lt : j.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hj]
  have j_lv : j.lastAcceptedVersion = (W.node n).lastAcceptedVersionOrMetadataVersion := by rw [hj]
  clear hcs hj h
  -- the soup: one new join
  have hg : ∀ m, W.sent m → ((W.set n cs').send (.join j)).sent m := fun _ h => Or.inl h
  have hpr : ∀ src s pt pv, ((W.set n cs').send (.join j)).sent (.publishRequest src s pt pv) →
      W.sent (.publishRequest src s pt pv) := by
    intro _ _ _ _ h; rcases h with h | h
    · exact h
    · cases h
  have hrs : ∀ a d r, ((W.set n cs').send (.join j)).sent (.publishResponse a d r) →
      W.sent (.publishResponse a d r) := by
    intro _ _ _ h; rcases h with h | h
    · exact h
    · cases h
  have hac : ∀ c, ((W.set n cs').send (.join j)).sent (.applyCommit c) → W.sent (.applyCommit c) := by
    intro _ h; rcases h with h | h
    · exact h
    · cases h
  have hjn : ∀ j', ((W.set n cs').send (.join j)).sent (.join j') → W.sent (.join j') ∨ j' = j := by
    intro j' h; rcases h with h | h
    · exact Or.inl h
    · cases h; exact Or.inr rfl
  have hnode : ∀ m, m ≠ n → ((W.set n cs').send (.join j)).node m = W.node m :=
    fun m hm => set_node_ne _ _ _ _ hm
  have hnode_n : ((W.set n cs').send (.join j)).node n = cs' := set_node_self _ _ _
  -- every response has a term ≥ 1
  have hrpos : ∀ a d (r : PublishResponse), W.sent (.publishResponse a d r) → 1 ≤ r.term := by
    intro a d r hr
    obtain ⟨s, pt, pv, hs, hst, -⟩ := hinv.response_published a d r hr
    have := (hinv.pub_wf _ _ _ _ hs).2.1
    omega
  -- an eligible node's old joins are for terms below t
  have hold : ∀ j', W.sent (.join j') → j'.sourceNode.id = n → P.eligible n = true → j'.term < t := by
    intro j' hj' hs he
    have := hinv.join_term_le j' hj' (by rw [hs]; exact he)
    rw [hs] at this
    omega
  have hwon : ∀ a t', Won P ((W.set n cs').send (.join j)) a t' → Won P W a t' := by
    rintro a t' ⟨he, hw | ⟨s, pt, pv, hs, hst⟩⟩
    · by_cases ha : a = n
      · subst ha; rw [hnode_n, e_ew] at hw; cases hw.1
      · rw [hnode a ha] at hw; exact ⟨he, Or.inl hw⟩
    · exact ⟨he, Or.inr ⟨s, pt, pv, hpr _ _ _ _ hs, hst⟩⟩
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := ?_, join_term_le := ?_, join_unique := ?_,
      join_after_response := ?_, response_le := ?_, response_published := ?_, pub_wf := ?_, pub_parent := ?_,
      pub_unique := ?_, pub_rooted := ?_, pub_same_term := ?_, pub_voters := ?_, pub_election := ?_,
      commit_quorum := ?_, won_unique := ?_, pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_,
      leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ln]; exact hinv.localNode_eq m
    · rw [hnode m hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lpv, e_pv]; intro _; exact ⟨rfl, rfl⟩
    · rw [hnode m hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv]; intro h; exact absurd rfl h
    · rw [hnode m hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ct]; intro _; omega
    · rw [hnode m hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, isQuorum_empty]; intro _ h; cases h.1
    · rw [hnode m hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv]; intro h; cases h
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, j', hj', h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j', hg _ hj', h1⟩
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_pv]; intro h; cases h
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, h1⟩ := hinv.publishVotes_sent m x hx
      exact ⟨he, hg _ h1⟩
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ct, e_lat]; have := hinv.term_le m hme; omega
    · rw [hnode m hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_lav, e_lcc, e_lac]
      exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
    · rw [hnode m hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j' hj'
    rcases hjn j' hj' with hj' | rfl
    · exact hinv.join_wf j' hj'
    · rw [j_srcid, j_src, j_tgt]; exact ⟨rfl, hsrc⟩
  · intro j' hj' hje
    by_cases hm : j'.sourceNode.id = n
    · rw [hm, hnode_n, e_ct]
      rcases hjn j' hj' with hj' | rfl
      · exact Nat.le_of_lt (hold j' hj' hm (by rw [← hm]; exact hje))
      · rw [j_term]; exact Nat.le_refl _
    · rw [hnode _ hm]
      rcases hjn j' hj' with hj' | rfl
      · exact hinv.join_term_le j' hj' hje
      · exact absurd j_srcid hm
  · intro j₁ j₂ h₁ h₂ he hs ht
    rcases hjn j₁ h₁ with h₁' | rfl <;> rcases hjn j₂ h₂ with h₂' | rfl
    · exact hinv.join_unique j₁ j₂ h₁' h₂' he hs ht
    · rw [j_srcid] at hs; rw [hs] at he
      have := hold j₁ h₁' hs he
      omega
    · rw [j_srcid] at hs he
      have := hold j₂ h₂' hs.symm he
      omega
    · rfl
  · intro j' a d r hj' hr hs ha hrt
    have hr0 := hrs a d r hr
    rcases hjn j' hj' with hj0 | rfl
    · exact hinv.join_after_response j' a d r hj0 hr0 hs ha hrt
    · rw [j_srcid] at hs; subst hs
      obtain ⟨-, h2⟩ := hinv.response_le n d r hr0 ha
      have h1 := hrpos _ _ _ hr0
      rw [j_lt, j_lv]
      unfold KeyLE at h2 ⊢
      have hpos : (W.node n).lastAcceptedTerm ≠ 0 := by omega
      rw [vomv_of_pos _ hpos]
      exact h2
  · intro a d r hr ha
    have hr0 := hrs a d r hr
    by_cases hm : a = n
    · subst hm; rw [hnode_n, e_ct, e_lat, e_lav]
      obtain ⟨h1, h2⟩ := hinv.response_le a d r hr0 ha
      exact ⟨by omega, h2⟩
    · rw [hnode a hm]; exact hinv.response_le a d r hr0 ha
  · intro a d r hr
    obtain ⟨s, pt, pv, hs, h1, h2⟩ := hinv.response_published a d r (hrs a d r hr)
    exact ⟨s, pt, pv, hg _ hs, h1, h2⟩
  · intro src s pt pv hs; exact hinv.pub_wf src s pt pv (hpr _ _ _ _ hs)
  · intro src s pt pv hs hpt
    obtain ⟨src', s', pt', pv', hs', h1, h2, h3, h4⟩ := hinv.pub_parent src s pt pv (hpr _ _ _ _ hs) hpt
    exact ⟨src', s', pt', pv', hg _ hs', h1, h2, h3.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩), h4⟩
  · intro src s pt pv src' s' pt' pv' hs hs'
    exact hinv.pub_unique src s pt pv src' s' pt' pv' (hpr _ _ _ _ hs) (hpr _ _ _ _ hs')
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv (hpr _ _ _ _ hs)
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' (hpr _ _ _ _ hs) (hpr _ _ _ _ hs') ht).imp
      (descends_mono hg) (descends_mono hg)
  · intro src s pt pv hs
    obtain ⟨J, h1, h2, h3⟩ := hinv.pub_voters src s pt pv (hpr _ _ _ _ hs)
    exact ⟨J, joinVoters_mono hg h1, h2, h3⟩
  · intro src s pt pv hs hpt
    obtain ⟨y, J, h1⟩ := hinv.pub_election src s pt pv (hpr _ _ _ _ hs) hpt
    exact ⟨y, J, electionRecord_mono hg h1⟩
  · intro c hc
    obtain ⟨src, s, pt, pv, hs, h1, h2, A, hA, h3, h4⟩ := hinv.commit_quorum c (hac c hc)
    refine ⟨src, s, pt, pv, hg _ hs, h1, h2, A, respVoters_mono hg hA, h3, ?_⟩
    rcases h4 with h4 | ⟨h4, src', s', pt', pv', hs', h5, h6, h7⟩
    · exact Or.inl h4
    · exact Or.inr ⟨committed_mono hg h4, src', s', pt', pv', hg _ hs', h5, h6, h7⟩
  · intro a b t' ha hb
    exact hinv.won_unique a b t' (hwon a t' ha) (hwon b t' hb)
  · intro src' s pt pv hs
    have hs0 := hpr _ _ _ _ hs
    by_cases hm : src' = n
    · subst hm; rw [hnode_n, e_ct]
      left
      rcases hinv.pub_source_term src' s pt pv hs0 with h | ⟨h, -⟩ <;> omega
    · rw [hnode src' hm]; exact hinv.pub_source_term src' s pt pv hs0
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv (hpr _ _ _ _ hs) ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]
      intro hw hne
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne
      exact ⟨s, hg _ hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew]; intro h; cases h
    · rw [hnode m hm]
      intro hw hv
      rcases hinv.leader_settled m hw hv with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun src s pt pv hs => h2 src s pt pv (hpr _ _ _ _ hs)⟩

/-- `join` preserves the invariant. The only hard case is an election win: no publication of the term exists and no
other node has won it, by `inv_election_unique` (two election records of a term have the same candidate), applied to
the winner's new record and to the first publication of the term or the other winner's record. -/
theorem OpenSearchSafety.inv_join {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool) (hsent : W.sent (.join j))
    (hdest : j.targetNode.id = n) (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
    Inv P (W.set n cs') := by
  obtain ⟨hjt, hsj, hlacne, hguard, hcs⟩ := spec_join _ _ _ _ _ h
  clear h
  generalize hvotes : ((W.node n).joinVotes.addVote j.sourceNode).1 = votes at hcs
  generalize hwon : (W.node n).isElectionQuorum P.strategy votes = won at hcs
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = (W.node n).currentTerm := by rw [hcs]
  have e_ew : cs'.electionWon = won := by rw [hcs]
  have e_jv : cs'.joinVotes = votes := by rw [hcs]
  have e_pv : cs'.publishVotes = (W.node n).publishVotes := by rw [hcs]
  have e_sj : cs'.startedJoinSinceLastReboot = (W.node n).startedJoinSinceLastReboot := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = if won = true ∧ (W.node n).electionWon = false then
      (W.node n).lastAcceptedVersion else (W.node n).lastPublishedVersion := by rw [hcs]
  have e_lpc : cs'.lastPublishedConfiguration = (W.node n).lastPublishedConfiguration := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hcs]; rfl
  have e_lav : cs'.lastAcceptedVersion = (W.node n).lastAcceptedVersion := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := by rw [hcs]; rfl
  have e_lac : cs'.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; rfl
  clear hcs
  have hg : ∀ m, W.sent m → (W.set n cs').sent m := fun _ h => h
  have hne : P.eligible n = true := by have := (hinv.join_wf j hsent).2; rwa [hdest] at this
  have hjel : j.sourceNode.isClusterManagerNode = P.eligible j.sourceNode.id :=
    congrArg DiscoveryNode.isClusterManagerNode (hinv.join_wf j hsent).1
  -- the votes are the old ones and the new voter, if eligible
  have hmem : ∀ x, x ∈ votes.nodes →
      x ∈ (W.node n).joinVotes.nodes ∨ (x = j.sourceNode.id ∧ P.eligible x = true) := by
    intro x hx
    rw [← hvotes, addVote_mem] at hx
    rcases hx with hx | ⟨rfl, hc⟩
    · exact Or.inl hx
    · exact Or.inr ⟨rfl, hjel ▸ hc⟩
  have hsub : ∀ x, x ∈ (W.node n).joinVotes.nodes → x ∈ votes.nodes := by
    intro x hx; rw [← hvotes, addVote_mem]; exact Or.inl hx
  have hbelow : Below j.lastAcceptedTerm j.lastAcceptedVersion (W.node n).lastAcceptedTerm
      (W.node n).lastAcceptedVersion := by
    rcases hguard with hlt | ⟨heq, hle⟩
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      by_cases h0 : (W.node n).lastAcceptedTerm = 0
      · exact Or.inl h0
      · right; rw [vomv_of_pos _ h0] at hle; exact hle
  have hvotes_sent : ∀ x, x ∈ votes.nodes → P.eligible x = true ∧ ∃ j' : Join, W.sent (.join j') ∧
      j'.sourceNode.id = x ∧ j'.targetNode.id = n ∧ j'.term = (W.node n).currentTerm ∧
      Below j'.lastAcceptedTerm j'.lastAcceptedVersion (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion := by
    intro x hx
    rcases hmem x hx with hx | ⟨rfl, he⟩
    · exact hinv.joinVotes_sent n x hx
    · exact ⟨he, j, hsent, rfl, hdest, hjt, hbelow⟩
  have hwq : won = true ↔ (votes.isQuorum (W.node n).lastCommittedConfiguration = true ∧
      votes.isQuorum (W.node n).lastAcceptedConfiguration = true) := by
    rw [← hwon, hes]
    simp [CoordinationState.isElectionQuorum, ElectionStrategy.DEFAULT_INSTANCE]
  have hmono : (W.node n).electionWon = true → won = true := by
    intro hw
    obtain ⟨h1, h2⟩ := hinv.won_quorum n hw
    exact hwq.mpr ⟨quorum_mono _ _ _ hsub h1, quorum_mono _ _ _ hsub h2⟩
  have hctpos : 1 ≤ (W.node n).currentTerm := hinv.started_term_pos n hsj
  /- An election win: the node's accepted state is of an older term, no publication of the term exists, and no other
  node has won the term. -/
  have hnot_t : won = true → (W.node n).electionWon = false →
      (W.node n).lastAcceptedTerm ≠ (W.node n).currentTerm := by
    intro hw hew0 heq
    obtain ⟨-, hq⟩ := hwq.mp hw
    rcases hinv.accepted_realizes n hne with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, -, h3, -⟩
    · omega
    · omega
    · obtain ⟨J, hJ, -, hJq⟩ := hinv.pub_voters src₂ s₂ pt₂ pv₂ hs₂
      have hq' : s₂.lastAcceptedConfiguration.hasQuorum votes.nodes = true := by rw [← h3]; exact hq
      obtain ⟨x, -, hx1, hx2⟩ := quorum_intersect _ _ _ hq' hJq
      obtain ⟨hxe, j₁, hj₁, hs₁, ht₁, hterm₁, -⟩ := hvotes_sent x hx1
      obtain ⟨-, j₂, hj₂, hs₂', ht₂, hterm₂⟩ := hJ x hx2
      have hjj := hinv.join_unique j₁ j₂ hj₁ hj₂ (by rw [hs₁]; exact hxe) (hs₁.trans hs₂'.symm)
        (by rw [hterm₁, hterm₂, h1, heq])
      have hLn : src₂ = n := by rw [← ht₂, ← hjj, ht₁]
      subst hLn
      rcases hinv.pub_source_term src₂ s₂ pt₂ pv₂ hs₂ with hlt | ⟨-, hw' | hsj'⟩
      · rw [h1, heq] at hlt; omega
      · rw [hw'] at hew0; cases hew0
      · rw [hsj] at hsj'; cases hsj'
  have hrec_n : won = true → (W.node n).electionWon = false →
      ElectionRecord P W n (W.node n).currentTerm (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion
        (W.node n).lastCommittedConfiguration (W.node n).lastAcceptedConfiguration votes.nodes := by
    intro hw hew0
    obtain ⟨hq1, hq2⟩ := hwq.mp hw
    refine ⟨Nat.lt_of_le_of_ne (hinv.term_le n hne) (hnot_t hw hew0), ?_, hvotes_sent, hq1, hq2⟩
    rcases hinv.accepted_realizes n hne with ⟨-, -, h0⟩ | hr
    · rw [h0] at hlacne
      simp [VotingConfiguration.isEmpty, VotingConfiguration.EMPTY_CONFIG] at hlacne
    · exact hr
  have hno_pub : won = true → (W.node n).electionWon = false →
      ∀ src s pt pv, W.sent (.publishRequest src s pt pv) → s.term ≠ (W.node n).currentTerm := by
    intro hw hew0 src s pt pv hs hst
    obtain ⟨L, F, pt', pv', hF, hFt, hFpt, -⟩ := inv_reign_first P W hinv src s pt pv hs
    obtain ⟨y, J, hFrec⟩ := hinv.pub_election L F pt' pv' hF hFpt
    rw [hFt, hst] at hFrec
    have hLn := inv_election_unique P hP W hinv _ L n _ _ _ _ _ _ _ _ _ _ hFrec (hrec_n hw hew0)
    subst hLn
    rcases hinv.pub_source_term L F pt' pv' hF with hlt' | ⟨-, hw' | hsj'⟩
    · rw [hFt, hst] at hlt'; omega
    · rw [hw'] at hew0; cases hew0
    · rw [hsj] at hsj'; cases hsj'
  have hno_other : won = true → (W.node n).electionWon = false →
      ∀ m, m ≠ n → (W.node m).electionWon = true → (W.node m).currentTerm ≠ (W.node n).currentTerm := by
    intro hw hew0 m hm hwm hct
    have hme := inv_eligible_of_won P W hinv m hwm
    have hmpos := hinv.started_term_pos m (hinv.won_started m hwm)
    by_cases hlv : (W.node m).lastPublishedVersion = (W.node m).lastAcceptedVersion
    · rcases hinv.leader_settled m hwm hlv with ⟨hlt, -⟩ | ⟨hlt, -⟩
      · rcases hinv.accepted_realizes m hme with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, -⟩
        · omega
        · omega
        · exact hno_pub hw hew0 _ _ _ _ hs₂ (by rw [h1, hlt, hct])
      · obtain ⟨hq1, hq2⟩ := hinv.won_quorum m hwm
        have hrec_m : ElectionRecord P W m (W.node n).currentTerm (W.node m).lastAcceptedTerm
            (W.node m).lastAcceptedVersion (W.node m).lastCommittedConfiguration
            (W.node m).lastAcceptedConfiguration (W.node m).joinVotes.nodes := by
          refine ⟨by rw [← hct]; exact hlt, ?_, ?_, hq1, hq2⟩
          · rcases hinv.accepted_realizes m hme with ⟨-, -, h0⟩ | hr
            · unfold VoteCollection.isQuorum at hq2
              rw [h0, empty_no_quorum] at hq2
              cases hq2
            · exact hr
          · intro x hx
            obtain ⟨he, j', hj', h1, h2, h3, h4⟩ := hinv.joinVotes_sent m x hx
            exact ⟨he, j', hj', h1, h2, by rw [h3, hct], h4⟩
        exact hm (inv_election_unique P hP W hinv _ m n _ _ _ _ _ _ _ _ _ _ hrec_m (hrec_n hw hew0))
    · obtain ⟨s, hs, h1, -⟩ := hinv.leader_inflight m hwm hlv
      exact hno_pub hw hew0 _ _ _ _ hs (by rw [h1, hct])
  -- nobody had won the term before
  have hwon_new : won = true → (W.node n).electionWon = false → ∀ a, ¬ Won P W a (W.node n).currentTerm := by
    rintro hw hew0 a ⟨-, ⟨hwa, hcta⟩ | ⟨s, pt, pv, hs, hst⟩⟩
    · by_cases ha : a = n
      · subst ha; rw [hew0] at hwa; cases hwa
      · exact hno_other hw hew0 a ha hwa hcta
    · exact hno_pub hw hew0 _ _ _ _ hs hst
  have hwonW' : ∀ a t', Won P (W.set n cs') a t' → Won P W a t' ∨
      (a = n ∧ t' = (W.node n).currentTerm ∧ won = true ∧ (W.node n).electionWon = false) := by
    rintro a t' ⟨he, ⟨hwa, hcta⟩ | hp⟩
    · by_cases ha : a = n
      · subst ha
        rw [set_node_self, e_ew] at hwa
        rw [set_node_self, e_ct] at hcta
        by_cases hew : (W.node a).electionWon = true
        · exact Or.inl ⟨he, Or.inl ⟨hew, hcta⟩⟩
        · exact Or.inr ⟨rfl, hcta.symm, hwa, by simpa using hew⟩
      · rw [set_node_ne _ _ _ _ ha] at hwa hcta; exact Or.inl ⟨he, Or.inl ⟨hwa, hcta⟩⟩
    · exact Or.inl ⟨he, Or.inr hp⟩
  -- without a new win, the node's election state is unchanged
  have hold : ¬ (won = true ∧ (W.node n).electionWon = false) → won = true → (W.node n).electionWon = true := by
    intro hnew hw
    cases hew : (W.node n).electionWon
    · exact absurd ⟨hw, hew⟩ hnew
    · rfl
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := hinv.join_wf, join_term_le := ?_, join_unique := hinv.join_unique,
      join_after_response := hinv.join_after_response, response_le := ?_,
      response_published := hinv.response_published, pub_wf := hinv.pub_wf, pub_parent := hinv.pub_parent,
      pub_unique := hinv.pub_unique, pub_rooted := ?_, pub_same_term := ?_, pub_voters := hinv.pub_voters,
      pub_election := hinv.pub_election, commit_quorum := hinv.commit_quorum, won_unique := ?_,
      pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_, leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ln]; exact hinv.localNode_eq m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_pv]
      intro hw0
      have hnew : ¬ (won = true ∧ (W.node m).electionWon = false) := fun h => by rw [hw0] at h; cases h.1
      rw [if_neg hnew]
      have hew0 : (W.node m).electionWon = false := by
        cases hew : (W.node m).electionWon
        · rfl
        · rw [hmono hew] at hw0; cases hw0
      exact hinv.idle_of_not_won m hew0
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj]; intro _; exact hsj
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj]; intro _; exact hsj
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj, e_ct]; exact hinv.started_term_pos m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_jv, e_lcc, e_lac]; exact hwq.mp
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_jv, e_lcc, e_lac]
      intro hw0 hq
      rw [hwq.mpr hq] at hw0
      cases hw0
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv, e_ct, e_lat, e_lav]; exact hvotes_sent x
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.joinVotes_sent m x
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_pv, e_ct, e_lpv]
      intro hx
      by_cases hnew : won = true ∧ (W.node m).electionWon = false
      · rw [(hinv.idle_of_not_won m hnew.2).2] at hx; cases hx
      · rw [if_neg hnew]; exact hinv.publishVotes_sent m x hx
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.publishVotes_sent m x
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lat, e_ct]; exact hinv.term_le m hme
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lat, e_lav, e_lcc, e_lac]
      exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
    · rw [set_node_ne _ _ _ _ hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j' hj' hje
    by_cases hm : j'.sourceNode.id = n
    · rw [hm, set_node_self, e_ct]; have := hinv.join_term_le j' hj' hje; rw [hm] at this; exact this
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.join_term_le j' hj' hje
  · intro a d r hr ha
    by_cases hm : a = n
    · subst hm; rw [set_node_self, e_ct, e_lat, e_lav]; exact hinv.response_le a d r hr ha
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.response_le a d r hr ha
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv hs
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' hs hs' ht).imp (descends_mono hg) (descends_mono hg)
  · intro a b' t' ha hb
    rcases hwonW' a t' ha with ha' | ⟨han, hta, hw, hew0⟩
    · rcases hwonW' b' t' hb with hb' | ⟨-, htb, hw', hew0'⟩
      · exact hinv.won_unique a b' t' ha' hb'
      · rw [htb] at ha'; exact absurd ha' (hwon_new hw' hew0' a)
    · rcases hwonW' b' t' hb with hb' | ⟨hbn, -, -, -⟩
      · rw [hta] at hb'; exact absurd hb' (hwon_new hw hew0 b')
      · rw [han, hbn]
  · intro src s pt pv hs
    by_cases hm : src = n
    · subst hm; rw [set_node_self, e_ct, e_ew, e_sj]
      rcases hinv.pub_source_term src s pt pv hs with h | ⟨h1, hw | hsj'⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, Or.inl (hmono hw)⟩
      · exact Or.inr ⟨h1, Or.inr hsj'⟩
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.pub_source_term src s pt pv hs
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_ct, e_lpv, e_jv]
      intro hw src s pt pv hs ht
      by_cases hnew : won = true ∧ (W.node m).electionWon = false
      · exact absurd ht (hno_pub hnew.1 hnew.2 _ _ _ _ hs)
      · rw [if_neg hnew]
        obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m (hold hnew hw) src s pt pv hs ht
        exact ⟨h1, descends_mono hg h2, quorum_mono _ _ _ hsub h3, quorum_mono _ _ _ hsub h4⟩
    · rw [set_node_ne _ _ _ _ hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv hs ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lcc, e_lac]
      intro hw hne'
      by_cases hnew : won = true ∧ (W.node m).electionWon = false
      · rw [if_pos hnew] at hne'; exact absurd rfl hne'
      · rw [if_neg hnew] at hne' ⊢
        exact hinv.leader_inflight m (hold hnew hw) hne'
    · rw [set_node_ne _ _ _ _ hm]
      intro hw hne'
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne'
      exact ⟨s, hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lac]
      intro hw hv
      by_cases hnew : won = true ∧ (W.node m).electionWon = false
      · exact Or.inr ⟨Nat.lt_of_le_of_ne (hinv.term_le m hne) (hnot_t hnew.1 hnew.2),
          fun src s pt pv hs => hno_pub hnew.1 hnew.2 src s pt pv hs⟩
      · rw [if_neg hnew] at hv
        exact hinv.leader_settled m (hold hnew hw) hv
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.leader_settled m

/-- `clientValue` preserves the invariant. -/
theorem OpenSearchSafety.inv_clientValue {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (s : ClusterState V) (cs' : CoordinationState V) (p : PublishRequest V)
    (hcontract : (W.node n).clientValueContract s) (h : (W.node n).handleClientValue s = .ok (cs', p)) :
    Inv P ((W.set n cs').send (.publishRequest n p.acceptedState (W.node n).lastAcceptedTerm
      (W.node n).lastAcceptedVersion)) := by
  obtain ⟨hew, hlpv, hst, hsv, hreconf, hq, rfl, hcs⟩ := spec_clientValue _ _ _ _ h
  clear h
  have hlcc : s.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := hcontract
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = (W.node n).currentTerm := by rw [hcs]
  have e_ew : cs'.electionWon = (W.node n).electionWon := by rw [hcs]
  have e_jv : cs'.joinVotes = (W.node n).joinVotes := by rw [hcs]
  have e_pv : cs'.publishVotes = VoteCollection.empty := by rw [hcs]
  have e_sj : cs'.startedJoinSinceLastReboot = (W.node n).startedJoinSinceLastReboot := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = s.version := by rw [hcs]
  have e_lpc : cs'.lastPublishedConfiguration = s.lastAcceptedConfiguration := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hcs]; rfl
  have e_lav : cs'.lastAcceptedVersion = (W.node n).lastAcceptedVersion := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := by rw [hcs]; rfl
  have e_lac : cs'.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; rfl
  clear hcs
  have hne : P.eligible n = true := inv_eligible_of_won P W hinv n hew
  have hctpos : 1 ≤ (W.node n).currentTerm := hinv.started_term_pos n (hinv.won_started n hew)
  obtain ⟨hq1, hq2⟩ := hinv.won_quorum n hew
  -- the leader's accepted state realizes its key
  have hreal : Realizes P W (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion
      (W.node n).lastCommittedConfiguration (W.node n).lastAcceptedConfiguration := by
    rcases hinv.accepted_realizes n hne with ⟨-, -, h0⟩ | hr
    · unfold VoteCollection.isQuorum at hq2
      rw [h0, empty_no_quorum] at hq2
      cases hq2
    · exact hr
  -- the soup: one new publication, of term `t` = the current term, on top of the accepted key `(lat, lav)`
  generalize hW' : (W.set n cs').send (.publishRequest n s (W.node n).lastAcceptedTerm
    (W.node n).lastAcceptedVersion) = W'
  have hg : ∀ m, W.sent m → W'.sent m := fun _ h => by rw [← hW']; exact Or.inl h
  have hnew : W'.sent (.publishRequest n s (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion) := by
    rw [← hW']; exact Or.inr rfl
  have hpr : ∀ a s' pt' pv', W'.sent (.publishRequest a s' pt' pv') → W.sent (.publishRequest a s' pt' pv') ∨
      (a = n ∧ s' = s ∧ pt' = (W.node n).lastAcceptedTerm ∧ pv' = (W.node n).lastAcceptedVersion) := by
    intro a s' pt' pv' h'; rw [← hW'] at h'
    rcases h' with h' | h'
    · exact Or.inl h'
    · cases h'; exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
  have hrs : ∀ a d r, W'.sent (.publishResponse a d r) → W.sent (.publishResponse a d r) := by
    intro _ _ _ h'; rw [← hW'] at h'
    rcases h' with h' | h'
    · exact h'
    · cases h'
  have hjn : ∀ j, W'.sent (.join j) → W.sent (.join j) := by
    intro _ h'; rw [← hW'] at h'
    rcases h' with h' | h'
    · exact h'
    · cases h'
  have hac : ∀ c, W'.sent (.applyCommit c) → W.sent (.applyCommit c) := by
    intro _ h'; rw [← hW'] at h'
    rcases h' with h' | h'
    · exact h'
    · cases h'
  have hnode : ∀ m, m ≠ n → W'.node m = W.node m := fun m hm => by rw [← hW']; exact set_node_ne _ _ _ _ hm
  have hnode_n : W'.node n = cs' := by rw [← hW']; exact set_node_self _ _ _
  have hparent : Parent W' (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion s.term s.version :=
    ⟨n, s, hnew, rfl, rfl⟩
  -- the publications of the term so far descend to the accepted key (the leader's previous publication)
  have hold_term : ∀ a s' pt' pv', W.sent (.publishRequest a s' pt' pv') → s'.term = s.term →
      s'.version ≤ (W.node n).lastAcceptedVersion ∧
      Descends W s'.term s'.version (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion := by
    intro a s' pt' pv' hs' ht'
    rcases hinv.leader_settled n hew hlpv with ⟨hlt, -⟩ | ⟨-, hnone⟩
    · obtain ⟨h1, h2, -, -⟩ := hinv.leader_pubs n hew a s' pt' pv' hs' (ht'.trans hst)
      rw [hlpv] at h1 h2
      rw [hlt]
      exact ⟨h1, h2⟩
    · exact absurd (ht'.trans hst) (hnone a s' pt' pv' hs')
  -- other leaders are in other terms
  have hother : ∀ m, m ≠ n → (W.node m).electionWon = true → (W.node m).currentTerm ≠ s.term := by
    intro m hm hwm hct
    exact hm (hinv.won_unique m n _ (inv_won_of_electionWon P W hinv m hwm)
      (by rw [hct, hst]; exact inv_won_of_electionWon P W hinv n hew))
  have hwon : ∀ a t, Won P W' a t → Won P W a t := by
    rintro a t ⟨he, hw | ⟨s', pt', pv', hs', hst'⟩⟩
    · by_cases ha : a = n
      · subst ha; rw [hnode_n, e_ew, e_ct] at hw; exact ⟨he, Or.inl hw⟩
      · rw [hnode a ha] at hw; exact ⟨he, Or.inl hw⟩
    · rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, -, -⟩
      · exact ⟨he, Or.inr ⟨s', pt', pv', hs0, hst'⟩⟩
      · rw [← hst', hst]; exact inv_won_of_electionWon P W hinv a hew
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := ?_, join_term_le := ?_, join_unique := ?_,
      join_after_response := ?_, response_le := ?_, response_published := ?_, pub_wf := ?_, pub_parent := ?_,
      pub_unique := ?_, pub_rooted := ?_, pub_same_term := ?_, pub_voters := ?_, pub_election := ?_,
      commit_quorum := ?_, won_unique := ?_, pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_,
      leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ln]; exact hinv.localNode_eq m
    · rw [hnode m hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, hew]; intro h'; cases h'
    · rw [hnode m hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_sj]; exact hinv.won_started m
    · rw [hnode m hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, e_sj]; exact hinv.votes_started m
    · rw [hnode m hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_sj, e_ct]; exact hinv.started_term_pos m
    · rw [hnode m hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_jv, e_lcc, e_lac]; exact hinv.won_quorum m
    · rw [hnode m hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_jv, e_lcc, e_lac]; exact hinv.not_won_no_quorum m
    · rw [hnode m hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, e_ct, e_lat, e_lav]
      intro hx
      obtain ⟨he, j, hj, h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j, hg _ hj, h1⟩
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, j, hj, h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j, hg _ hj, h1⟩
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_pv]; intro hx; cases hx
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, h1⟩ := hinv.publishVotes_sent m x hx
      exact ⟨he, hg _ h1⟩
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_ct]; exact hinv.term_le m hme
    · rw [hnode m hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_lav, e_lcc, e_lac]
      exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
    · rw [hnode m hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j hj; exact hinv.join_wf j (hjn j hj)
  · intro j hj hje
    by_cases hm : j.sourceNode.id = n
    · rw [hm, hnode_n, e_ct]; have := hinv.join_term_le j (hjn j hj) hje; rw [hm] at this; exact this
    · rw [hnode _ hm]; exact hinv.join_term_le j (hjn j hj) hje
  · intro j j' hj hj'; exact hinv.join_unique j j' (hjn j hj) (hjn j' hj')
  · intro j a d r hj hr; exact hinv.join_after_response j a d r (hjn j hj) (hrs a d r hr)
  · intro a d r hr ha
    by_cases hm : a = n
    · subst hm; rw [hnode_n, e_ct, e_lat, e_lav]; exact hinv.response_le a d r (hrs a d r hr) ha
    · rw [hnode a hm]; exact hinv.response_le a d r (hrs a d r hr) ha
  · intro a d r hr
    obtain ⟨s', pt', pv', hs', h1, h2⟩ := hinv.response_published a d r (hrs a d r hr)
    exact ⟨s', pt', pv', hg _ hs', h1, h2⟩
  · intro a s' pt' pv' hs'
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · exact hinv.pub_wf _ _ _ _ hs0
    · refine ⟨hne, by omega, by have := hinv.term_le a hne; omega, hsv, ?_⟩
      intro h0
      rcases hreal with ⟨-, hxy, hX⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, -⟩
      · rw [hlcc]; exact hX
      · have := (hinv.pub_wf _ _ _ _ hs₂).2.1; omega
  · intro a s' pt' pv' hs' hpt
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨src', s'', pt'', pv'', hs'', h1, h2, h3, h4⟩ := hinv.pub_parent _ _ _ _ hs0 hpt
      exact ⟨src', s'', pt'', pv'', hg _ hs'', h1, h2, h3.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩), h4⟩
    · rcases hreal with ⟨h0, -⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, h2, h3, h4⟩
      · omega
      · refine ⟨src₂, s₂, pt₂, pv₂, hg _ hs₂, h1, h2, ?_, ?_⟩
        · rw [hlcc]; exact h4.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩)
        · intro hac'
          rcases hreconf with hr | hr
          · exact absurd (hr.trans h3) hac'
          · rw [hlcc, hr, h3]
  · intro a₁ s₁ pt₁ pv₁ a₂ s₂ pt₂ pv₂ h₁ h₂ ht hv
    rcases hpr _ _ _ _ h₁ with h₁' | ⟨rfl, rfl, rfl, rfl⟩ <;>
      rcases hpr _ _ _ _ h₂ with h₂' | ⟨rfl, rfl, rfl, rfl⟩
    · exact hinv.pub_unique _ _ _ _ _ _ _ _ h₁' h₂' ht hv
    · have := (hold_term _ _ _ _ h₁' ht).1; omega
    · have := (hold_term _ _ _ _ h₂' ht.symm).1; omega
    · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro a s' pt' pv' hs'
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨v₀, h'⟩ := hinv.pub_rooted _ _ _ _ hs0
      exact ⟨v₀, descends_mono hg h'⟩
    · rcases hreal with ⟨h0, -⟩ | ⟨src₂, s₂, pt₂, pv₂, hs₂, h1, h2, -⟩
      · refine ⟨(W.node a).lastAcceptedVersion, .step _ _ _ _ _ _ ?_ hparent⟩
        rw [← h0]; exact .refl _ _
      · obtain ⟨v₀, h'⟩ := hinv.pub_rooted _ _ _ _ hs₂
        rw [h1, h2] at h'
        exact ⟨v₀, .step _ _ _ _ _ _ (descends_mono hg h') hparent⟩
  · intro a₁ s₁ pt₁ pv₁ a₂ s₂ pt₂ pv₂ h₁ h₂ ht
    rcases hpr _ _ _ _ h₁ with h₁' | ⟨rfl, rfl, rfl, rfl⟩ <;>
      rcases hpr _ _ _ _ h₂ with h₂' | ⟨rfl, rfl, rfl, rfl⟩
    · exact (hinv.pub_same_term _ _ _ _ _ _ _ _ h₁' h₂' ht).imp (descends_mono hg) (descends_mono hg)
    · exact Or.inl (.step _ _ _ _ _ _ (descends_mono hg (hold_term _ _ _ _ h₁' ht).2) hparent)
    · exact Or.inr (.step _ _ _ _ _ _ (descends_mono hg (hold_term _ _ _ _ h₂' ht.symm).2) hparent)
    · exact Or.inl (.refl _ _)
  · intro a s' pt' pv' hs'
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨J, h1, h2, h3⟩ := hinv.pub_voters _ _ _ _ hs0
      exact ⟨J, joinVoters_mono hg h1, h2, h3⟩
    · refine ⟨(W.node a).joinVotes.nodes, ?_, by rw [hlcc]; exact hq1, hq⟩
      intro x hx
      obtain ⟨he, j, hj, h1, h2, h3, -⟩ := hinv.joinVotes_sent a x hx
      exact ⟨he, j, hg _ hj, h1, h2, by rw [h3, hst]⟩
  · intro a s' pt' pv' hs' hpt
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨y, J, h1⟩ := hinv.pub_election _ _ _ _ hs0 hpt
      exact ⟨y, J, electionRecord_mono hg h1⟩
    · refine ⟨(W.node a).lastAcceptedConfiguration, (W.node a).joinVotes.nodes, hpt,
        by rw [hlcc]; exact realizes_mono hg hreal, ?_, by rw [hlcc]; exact hq1, hq2⟩
      intro x hx
      obtain ⟨he, j, hj, h1, h2, h3, h4⟩ := hinv.joinVotes_sent a x hx
      exact ⟨he, j, hg _ hj, h1, h2, by rw [h3, hst], h4⟩
  · intro c hc
    obtain ⟨src, s', pt, pv, hs', h1, h2, A, hA, h3, h4⟩ := hinv.commit_quorum c (hac c hc)
    refine ⟨src, s', pt, pv, hg _ hs', h1, h2, A, respVoters_mono hg hA, h3, ?_⟩
    rcases h4 with h4 | ⟨h4, src', s'', pt', pv', hs'', h5, h6, h7⟩
    · exact Or.inl h4
    · exact Or.inr ⟨committed_mono hg h4, src', s'', pt', pv', hg _ hs'', h5, h6, h7⟩
  · intro a b t ha hb
    exact hinv.won_unique a b t (hwon a t ha) (hwon b t hb)
  · intro a s' pt' pv' hs'
    rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
    · by_cases hm : a = n
      · subst hm; rw [hnode_n, e_ct, e_ew, e_sj]; exact hinv.pub_source_term _ _ _ _ hs0
      · rw [hnode a hm]; exact hinv.pub_source_term _ _ _ _ hs0
    · rw [hnode_n, e_ct, e_ew]; exact Or.inr ⟨hst, Or.inl hew⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_ct, e_lpv, e_jv]
      intro _ a s' pt' pv' hs' ht'
      rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := hold_term _ _ _ _ hs0 (ht'.trans hst.symm)
        obtain ⟨-, -, h3, h4⟩ := hinv.leader_pubs m hew _ _ _ _ hs0 ht'
        refine ⟨by omega, ?_, h3, h4⟩
        rw [← hst]
        exact .step _ _ _ _ _ _ (descends_mono hg h2) hparent
      · exact ⟨Int.le_refl _, by rw [← hst]; exact .refl _ _, by rw [hlcc]; exact hq1, hq⟩
    · rw [hnode m hm]
      intro hw a s' pt' pv' hs' ht'
      rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw _ _ _ _ hs0 ht'
        exact ⟨h1, descends_mono hg h2, h3, h4⟩
      · exact absurd ht'.symm (hother m hm hw)
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lcc]
      intro _ _
      exact ⟨s, hnew, hst, rfl, rfl, Or.inl hlcc.symm⟩
    · rw [hnode m hm]
      intro hw hne'
      obtain ⟨s', hs', h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne'
      exact ⟨s', hg _ hs', h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lpv, e_lav]
      intro _ hv
      omega
    · rw [hnode m hm]
      intro hw hv
      rcases hinv.leader_settled m hw hv with h' | ⟨h1, h2⟩
      · exact Or.inl h'
      · refine Or.inr ⟨h1, fun a s' pt' pv' hs' => ?_⟩
        rcases hpr _ _ _ _ hs' with hs0 | ⟨rfl, rfl, rfl, rfl⟩
        · exact h2 _ _ _ _ hs0
        · exact fun ht' => hother m hm hw ht'.symm

/-- `publish` preserves the invariant. -/
theorem OpenSearchSafety.inv_publish {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (cs' : CoordinationState V) (r : PublishResponse)
    (hsent : W.sent (.publishRequest src s pt pv)) (h : (W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)) :
    Inv P ((W.set n cs').send (.publishResponse n src r)) := by
  obtain ⟨hst, hfresh, hr, hcs⟩ := spec_publish _ _ _ _ h
  clear h
  have hst : s.term = (W.node n).currentTerm := hst
  obtain ⟨hsrce, hspos, -, -, -⟩ := hinv.pub_wf src s pt pv hsent
  have hfresh' : ¬ (s.term = (W.node n).lastAcceptedTerm ∧ s.version ≤ (W.node n).lastAcceptedVersion) := by
    rcases hfresh with h0 | h0
    · have : s.term = 0 := h0
      omega
    · exact h0
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = (W.node n).currentTerm := by rw [hcs]
  have e_ew : cs'.electionWon = (W.node n).electionWon := by rw [hcs]
  have e_jv : cs'.joinVotes = (W.node n).joinVotes := by rw [hcs]
  have e_pv : cs'.publishVotes = (W.node n).publishVotes := by rw [hcs]
  have e_sj : cs'.startedJoinSinceLastReboot = (W.node n).startedJoinSinceLastReboot := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = (W.node n).lastPublishedVersion := by rw [hcs]
  have e_lpc : cs'.lastPublishedConfiguration = (W.node n).lastPublishedConfiguration := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = s.term := by rw [hcs]; rfl
  have e_lav : cs'.lastAcceptedVersion = s.version := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = s.lastCommittedConfiguration := by rw [hcs]; rfl
  have e_lac : cs'.lastAcceptedConfiguration = s.lastAcceptedConfiguration := by rw [hcs]; rfl
  clear hcs
  -- the soup: one new publish response
  have hg : ∀ m, W.sent m → ((W.set n cs').send (.publishResponse n src r)).sent m := fun _ h => Or.inl h
  have hpr : ∀ a s' pt' pv', ((W.set n cs').send (.publishResponse n src r)).sent (.publishRequest a s' pt' pv') →
      W.sent (.publishRequest a s' pt' pv') := by
    intro _ _ _ _ h; rcases h with h | h
    · exact h
    · cases h
  have hjn : ∀ j, ((W.set n cs').send (.publishResponse n src r)).sent (.join j) → W.sent (.join j) := by
    intro _ h; rcases h with h | h
    · exact h
    · cases h
  have hac : ∀ c, ((W.set n cs').send (.publishResponse n src r)).sent (.applyCommit c) →
      W.sent (.applyCommit c) := by
    intro _ h; rcases h with h | h
    · exact h
    · cases h
  have hrs : ∀ a d r', ((W.set n cs').send (.publishResponse n src r)).sent (.publishResponse a d r') →
      W.sent (.publishResponse a d r') ∨ (a = n ∧ d = src ∧ r' = r) := by
    intro a d r' h; rcases h with h | h
    · exact Or.inl h
    · cases h; exact Or.inr ⟨rfl, rfl, rfl⟩
  have hnode : ∀ m, m ≠ n → ((W.set n cs').send (.publishResponse n src r)).node m = W.node m :=
    fun m hm => set_node_ne _ _ _ _ hm
  have hnode_n : ((W.set n cs').send (.publishResponse n src r)).node n = cs' := set_node_self _ _ _
  -- an eligible node's accepted key strictly increases
  have hinc : P.eligible n = true → (W.node n).lastAcceptedTerm < s.term ∨
      ((W.node n).lastAcceptedTerm = s.term ∧ (W.node n).lastAcceptedVersion < s.version) := by
    intro hne
    have := hinv.term_le n hne
    by_cases heq : (W.node n).lastAcceptedTerm = s.term
    · exact Or.inr ⟨heq, by have := fun h => hfresh' ⟨heq.symm, h⟩; omega⟩
    · exact Or.inl (by omega)
  -- a node holding a vote is eligible
  have helig : ∀ x, x ∈ (W.node n).joinVotes.nodes → P.eligible n = true := by
    intro x hx
    obtain ⟨-, j, hj, -, htgt, -⟩ := hinv.joinVotes_sent n x hx
    have := (hinv.join_wf j hj).2; rwa [htgt] at this
  -- an elected node accepts only its own publications
  have hsrc : (W.node n).electionWon = true → src = n := by
    intro hw
    exact hinv.won_unique src n s.term ⟨hsrce, Or.inr ⟨s, pt, pv, hsent, rfl⟩⟩
      (by rw [hst]; exact inv_won_of_electionWon P W hinv n hw)
  -- an elected node accepts exactly its publication in flight
  have hlead : (W.node n).electionWon = true → (W.node n).lastPublishedVersion = s.version ∧
      (W.node n).lastPublishedConfiguration = s.lastAcceptedConfiguration := by
    intro hw
    have hne := inv_eligible_of_won P W hinv n hw
    have hsn := hsrc hw
    obtain ⟨hv, hd, -, -⟩ := hinv.leader_pubs n hw src s pt pv hsent hst
    have hlv : (W.node n).lastPublishedVersion ≠ (W.node n).lastAcceptedVersion := by
      intro hlv
      rcases hinv.leader_settled n hw hlv with ⟨hlt, -⟩ | ⟨-, hnone⟩
      · exact hfresh' ⟨hst.trans hlt.symm, by omega⟩
      · exact hnone src s pt pv hsent hst
    obtain ⟨C, hC, hCt, hCv, hlpc, -⟩ := hinv.leader_inflight n hw hlv
    have hsv : s.version = (W.node n).lastPublishedVersion := by
      by_cases hne' : s.version = (W.node n).lastPublishedVersion
      · exact hne'
      exfalso
      have hd' := inv_descends_parent P W hinv _ _ n C _ _ hC (by rw [hCt, hCv]; exact hd)
        (fun h => hne' (h.2.trans hCv))
      rcases inv_descends_key P W hinv _ _ _ _ hd' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hfresh' ⟨h1, by omega⟩
      · have := hinv.term_le n hne
        exact hfresh' ⟨by omega, by omega⟩
    obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hsent hC (hst.trans hCt.symm) (hsv.trans hCv.symm)
    exact ⟨hsv.symm, hlpc⟩
  have hwon : ∀ a t, Won P ((W.set n cs').send (.publishResponse n src r)) a t → Won P W a t := by
    rintro a t ⟨he, hw | ⟨s', pt', pv', hs', hst'⟩⟩
    · by_cases ha : a = n
      · subst ha; rw [hnode_n, e_ew, e_ct] at hw; exact ⟨he, Or.inl hw⟩
      · rw [hnode a ha] at hw; exact ⟨he, Or.inl hw⟩
    · exact ⟨he, Or.inr ⟨s', pt', pv', hpr _ _ _ _ hs', hst'⟩⟩
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := ?_, join_term_le := ?_, join_unique := ?_,
      join_after_response := ?_, response_le := ?_, response_published := ?_, pub_wf := ?_, pub_parent := ?_,
      pub_unique := ?_, pub_rooted := ?_, pub_same_term := ?_, pub_voters := ?_, pub_election := ?_,
      commit_quorum := ?_, won_unique := ?_, pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_,
      leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ln]; exact hinv.localNode_eq m
    · rw [hnode m hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_lpv, e_pv]; exact hinv.idle_of_not_won m
    · rw [hnode m hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_sj]; exact hinv.won_started m
    · rw [hnode m hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, e_sj]; exact hinv.votes_started m
    · rw [hnode m hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_sj, e_ct]; exact hinv.started_term_pos m
    · rw [hnode m hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_jv, e_lcc, e_lac]
      intro hw
      obtain ⟨-, -, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv hsent hst
      exact ⟨h3, h4⟩
    · rw [hnode m hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_jv, e_lcc, e_lac]
      -- a voter common to the node's votes and the publisher's would have voted twice in the term
      rintro hew ⟨-, hq⟩
      have hne0 : (W.node m).joinVotes.nodes ≠ [] := ne_nil_of_hasQuorum _ _ hq
      obtain ⟨J, hJ, -, hJq⟩ := hinv.pub_voters src s pt pv hsent
      obtain ⟨x, -, hx1, hx2⟩ := quorum_intersect _ _ _ hq hJq
      obtain ⟨hxe, j₁, hj₁, hs₁, ht₁, hterm₁, -⟩ := hinv.joinVotes_sent m x hx1
      obtain ⟨-, j₂, hj₂, hs₂, ht₂, hterm₂⟩ := hJ x hx2
      have hjj := hinv.join_unique j₁ j₂ hj₁ hj₂ (by rw [hs₁]; exact hxe) (hs₁.trans hs₂.symm)
        (by rw [hterm₁, hterm₂, hst])
      have hLn : src = m := by rw [← ht₂, ← hjj, ht₁]
      subst hLn
      rcases hinv.pub_source_term src s pt pv hsent with hlt | ⟨-, hw' | hsj'⟩
      · omega
      · rw [hw'] at hew; cases hew
      · rw [hinv.votes_started src hne0] at hsj'; cases hsj'
    · rw [hnode m hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, e_ct, e_lat, e_lav]
      intro hx
      obtain ⟨he, j, hj, h1, h2, h3, hb⟩ := hinv.joinVotes_sent m x hx
      refine ⟨he, j, hg _ hj, h1, h2, h3, ?_⟩
      have := hinc (helig x hx)
      unfold Below at hb ⊢
      omega
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, j, hj, h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j, hg _ hj, h1⟩
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_pv, e_ct, e_lpv]
      intro hx
      obtain ⟨he, h1⟩ := hinv.publishVotes_sent m x hx
      exact ⟨he, hg _ h1⟩
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, h1⟩ := hinv.publishVotes_sent m x hx
      exact ⟨he, hg _ h1⟩
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_ct, hst]; exact Nat.le_refl _
    · rw [hnode m hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_lav, e_lcc, e_lac]
      exact Or.inr (Or.inr ⟨src, s, pt, pv, hg _ hsent, rfl, rfl, rfl, Or.inl rfl⟩)
    · rw [hnode m hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j hj; exact hinv.join_wf j (hjn j hj)
  · intro j hj hje
    by_cases hm : j.sourceNode.id = n
    · rw [hm, hnode_n, e_ct]; have := hinv.join_term_le j (hjn j hj) hje; rw [hm] at this; exact this
    · rw [hnode _ hm]; exact hinv.join_term_le j (hjn j hj) hje
  · intro j j' hj hj'; exact hinv.join_unique j j' (hjn j hj) (hjn j' hj')
  · intro j a d r' hj hr' hs ha hrt
    rcases hrs a d r' hr' with hr0 | ⟨rfl, -, rfl⟩
    · exact hinv.join_after_response j a d r' (hjn j hj) hr0 hs ha hrt
    · -- the node's joins are for terms at most its current term, the response's term
      have h1 := hinv.join_term_le j (hjn j hj) (by rw [hs]; exact ha)
      rw [hs] at h1
      rw [hr] at hrt
      have h2 : s.term < j.term := hrt
      omega
  · intro a d r' hr' ha
    rcases hrs a d r' hr' with hr0 | ⟨rfl, -, rfl⟩
    · by_cases hm : a = n
      · subst hm; rw [hnode_n, e_ct, e_lat, e_lav]
        obtain ⟨h1, h2⟩ := hinv.response_le a d r' hr0 ha
        refine ⟨h1, ?_⟩
        have := hinc ha
        unfold KeyLE at h2 ⊢
        omega
      · rw [hnode a hm]; exact hinv.response_le a d r' hr0 ha
    · rw [hnode_n, e_ct, e_lat, e_lav, hr]
      exact ⟨by dsimp only; omega, Or.inr ⟨rfl, Int.le_refl _⟩⟩
  · intro a d r' hr'
    rcases hrs a d r' hr' with hr0 | ⟨-, rfl, rfl⟩
    · obtain ⟨s', pt', pv', hs', h1, h2⟩ := hinv.response_published a d r' hr0
      exact ⟨s', pt', pv', hg _ hs', h1, h2⟩
    · exact ⟨s, pt, pv, hg _ hsent, by rw [hr], by rw [hr]⟩
  · intro src s pt pv hs; exact hinv.pub_wf src s pt pv (hpr _ _ _ _ hs)
  · intro src s pt pv hs hpt
    obtain ⟨src', s', pt', pv', hs', h1, h2, h3, h4⟩ := hinv.pub_parent src s pt pv (hpr _ _ _ _ hs) hpt
    exact ⟨src', s', pt', pv', hg _ hs', h1, h2, h3.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩), h4⟩
  · intro src s pt pv src' s' pt' pv' hs hs'
    exact hinv.pub_unique src s pt pv src' s' pt' pv' (hpr _ _ _ _ hs) (hpr _ _ _ _ hs')
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv (hpr _ _ _ _ hs)
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' (hpr _ _ _ _ hs) (hpr _ _ _ _ hs') ht).imp
      (descends_mono hg) (descends_mono hg)
  · intro src s pt pv hs
    obtain ⟨J, h1, h2, h3⟩ := hinv.pub_voters src s pt pv (hpr _ _ _ _ hs)
    exact ⟨J, joinVoters_mono hg h1, h2, h3⟩
  · intro src s pt pv hs hpt
    obtain ⟨y, J, h1⟩ := hinv.pub_election src s pt pv (hpr _ _ _ _ hs) hpt
    exact ⟨y, J, electionRecord_mono hg h1⟩
  · intro c hc
    obtain ⟨src, s, pt, pv, hs, h1, h2, A, hA, h3, h4⟩ := hinv.commit_quorum c (hac c hc)
    refine ⟨src, s, pt, pv, hg _ hs, h1, h2, A, respVoters_mono hg hA, h3, ?_⟩
    rcases h4 with h4 | ⟨h4, src', s', pt', pv', hs', h5, h6, h7⟩
    · exact Or.inl h4
    · exact Or.inr ⟨committed_mono hg h4, src', s', pt', pv', hg _ hs', h5, h6, h7⟩
  · intro a b t ha hb
    exact hinv.won_unique a b t (hwon a t ha) (hwon b t hb)
  · intro src' s' pt' pv' hs'
    have hs0 := hpr _ _ _ _ hs'
    by_cases hm : src' = n
    · subst hm; rw [hnode_n, e_ct, e_ew, e_sj]; exact hinv.pub_source_term src' s' pt' pv' hs0
    · rw [hnode src' hm]; exact hinv.pub_source_term src' s' pt' pv' hs0
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_ct, e_lpv, e_jv]
      intro hw src' s' pt' pv' hs' ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src' s' pt' pv' (hpr _ _ _ _ hs') ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
    · rw [hnode m hm]
      intro hw src' s' pt' pv' hs' ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src' s' pt' pv' (hpr _ _ _ _ hs') ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_lpv, e_lav]
      intro hw hne'
      exact absurd (hlead hw).1 hne'
    · rw [hnode m hm]
      intro hw hne'
      obtain ⟨s', hs', h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne'
      exact ⟨s', hg _ hs', h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lac]
      intro hw _
      exact Or.inl ⟨hst, (hlead hw).2⟩
    · rw [hnode m hm]
      intro hw hv
      rcases hinv.leader_settled m hw hv with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun src s pt pv hs => h2 src s pt pv (hpr _ _ _ _ hs)⟩

/-- `respond` preserves the invariant. -/
theorem OpenSearchSafety.inv_respond {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n src : NodeId) (r : PublishResponse) (cs' : CoordinationState V) (o : Option ApplyCommitRequest)
    (hsent : W.sent (.publishResponse src n r)) (h : (W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)) :
    Inv P (match o with
      | none => W.set n cs'
      | some c => (W.set n cs').send (.applyCommit c)) := by
  obtain ⟨hew, hrt, hrv, hcs, hc⟩ := spec_respond _ _ _ _ _ h
  have e_pv : cs'.publishVotes = ((W.node n).publishVotes.addVote (P.dn src)).1 := by rw [hcs]
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = (W.node n).currentTerm := by rw [hcs]
  have e_ew : cs'.electionWon = (W.node n).electionWon := by rw [hcs]
  have e_jv : cs'.joinVotes = (W.node n).joinVotes := by rw [hcs]
  have e_sj : cs'.startedJoinSinceLastReboot = (W.node n).startedJoinSinceLastReboot := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = (W.node n).lastPublishedVersion := by rw [hcs]
  have e_lpc : cs'.lastPublishedConfiguration = (W.node n).lastPublishedConfiguration := by rw [hcs]
  have e_las : cs'.lastAcceptedState = (W.node n).lastAcceptedState := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hcs]; rfl
  have e_lav : cs'.lastAcceptedVersion = (W.node n).lastAcceptedVersion := by rw [hcs]; rfl
  have e_lcc : cs'.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration := by rw [hcs]; rfl
  have e_lac : cs'.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; rfl
  have hne : P.eligible n = true := inv_eligible_of_won P W hinv n hew
  have hctpos : 1 ≤ (W.node n).currentTerm := hinv.started_term_pos n (hinv.won_started n hew)
  -- the publish votes are responses to the publication in flight
  have hA : RespVoters P W (W.node n).currentTerm (W.node n).lastPublishedVersion cs'.publishVotes.nodes := by
    intro x hx
    rw [e_pv, addVote_mem] at hx
    rcases hx with hx | ⟨rfl, hxe⟩
    · obtain ⟨he, hs⟩ := hinv.publishVotes_sent n x hx
      exact ⟨he, n, hs⟩
    · refine ⟨hxe, n, ?_⟩
      have hr : r = ⟨(W.node n).currentTerm, (W.node n).lastPublishedVersion⟩ := by rw [← hrt, ← hrv]
      rw [← hr]
      exact hsent
  -- (C1) a new commit is backed by the publish votes
  have hC1 : ∀ c, o = some c → ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ s.term = c.term ∧
      s.version = c.version ∧ ∃ A, RespVoters P W c.term c.version A ∧
        s.lastAcceptedConfiguration.hasQuorum A = true ∧
        (s.lastCommittedConfiguration.hasQuorum A = true ∨
          (Committed W pt pv ∧ ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ s'.term = pt ∧
            s'.version = pv ∧ s'.lastAcceptedConfiguration = s.lastAcceptedConfiguration)) := by
    intro c hco
    obtain ⟨rfl, hq1, hq2⟩ := hc c hco
    obtain ⟨C, pt, pv, hC, hCt, hCv⟩ := hinv.response_published src n r hsent
    rw [hrt] at hCt
    rw [hrv] at hCv
    -- the last published configuration is the publication's, and the last committed one is too, or (D1) ...
    have hcfg : (W.node n).lastPublishedConfiguration = C.lastAcceptedConfiguration ∧
        ((W.node n).lastCommittedConfiguration = C.lastCommittedConfiguration ∨
          ((W.node n).lastCommittedConfiguration = C.lastAcceptedConfiguration ∧ Committed W pt pv ∧
            ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ s'.term = pt ∧ s'.version = pv ∧
              s'.lastAcceptedConfiguration = C.lastAcceptedConfiguration) ∨
          Committed W (W.node n).currentTerm (W.node n).lastPublishedVersion) := by
      by_cases hlv : (W.node n).lastPublishedVersion = (W.node n).lastAcceptedVersion
      · rcases hinv.leader_settled n hew hlv with ⟨hlt, hlpc⟩ | ⟨-, hnone⟩
        · rcases hinv.accepted_realizes n hne with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨src', s', pt', pv', hs', h1, h2, h3, h4⟩
          · omega
          · omega
          · obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs' hC (by rw [h1, hCt, hlt])
              (by rw [h2, hCv, hlv])
            refine ⟨hlpc.trans h3, ?_⟩
            rcases h4 with h4 | ⟨-, h4⟩
            · exact Or.inl h4
            · rw [hlt, ← hlv] at h4; exact Or.inr (Or.inr h4)
        · exact absurd hCt (hnone _ _ _ _ hC)
      · obtain ⟨C', hC', h1, h2, h3, h4⟩ := hinv.leader_inflight n hew hlv
        obtain ⟨-, rfl, rfl, rfl⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hC' hC (h1.trans hCt.symm)
          (h2.trans hCv.symm)
        refine ⟨h3, ?_⟩
        rcases h4 with h4 | ⟨h4, h5, h6⟩
        · exact Or.inl h4
        · refine Or.inr (Or.inl ⟨h4, h5, ?_⟩)
          have hpos := (inv_committed_published P W hinv _ _ h5).1
          rcases hinv.accepted_realizes n hne with ⟨h0, -⟩ | ⟨h0, -⟩ |
              ⟨src', s', pt', pv', hs', h1', h2', h3', -⟩
          · omega
          · omega
          · exact ⟨src', s', pt', pv', hs', h1', h2', h3'.symm.trans h6⟩
    rcases hcfg with ⟨hlpc, hl | hl | hl⟩
    · refine ⟨n, C, pt, pv, hC, hCt, hCv, cs'.publishVotes.nodes, hA, ?_, ?_⟩
      · rw [← hlpc]; exact hq2
      · left; rw [← hl]; exact hq1
    · refine ⟨n, C, pt, pv, hC, hCt, hCv, cs'.publishVotes.nodes, hA, ?_, Or.inr hl.2⟩
      rw [← hlpc]; exact hq2
    · -- already committed: the earlier commit's record serves
      obtain ⟨src₀, h₀⟩ := hl
      exact hinv.commit_quorum ⟨src₀, (W.node n).currentTerm, (W.node n).lastPublishedVersion⟩ h₀
  suffices key : ∀ W' : Cluster V, W'.node = (W.set n cs').node →
      (∀ x, W'.sent x ↔ W.sent x ∨ ∃ c, o = some c ∧ x = .applyCommit c) → Inv P W' by
    cases o with
    | none =>
      exact key _ rfl (fun x => ⟨Or.inl, fun h => h.elim id (fun ⟨c, hc, _⟩ => by cases hc)⟩)
    | some c =>
      exact key _ rfl (fun x => ⟨fun h => h.elim Or.inl (fun h => Or.inr ⟨c, rfl, h⟩),
        fun h => h.elim Or.inl (fun ⟨c', hc', hx⟩ => Or.inr (by cases hc'; exact hx))⟩)
  intro W' hWn hWs
  have hg : ∀ m, W.sent m → W'.sent m := fun m h => (hWs m).mpr (Or.inl h)
  have hnode : ∀ m, m ≠ n → W'.node m = W.node m := fun m hm => by rw [hWn]; exact set_node_ne _ _ _ _ hm
  have hnode_n : W'.node n = cs' := by rw [hWn]; exact set_node_self _ _ _
  have hpr : ∀ src s pt pv, W'.sent (.publishRequest src s pt pv) → W.sent (.publishRequest src s pt pv) := by
    intro _ _ _ _ h
    rcases (hWs _).mp h with h | ⟨_, _, h⟩
    · exact h
    · cases h
  have hrs : ∀ a d r, W'.sent (.publishResponse a d r) → W.sent (.publishResponse a d r) := by
    intro _ _ _ h
    rcases (hWs _).mp h with h | ⟨_, _, h⟩
    · exact h
    · cases h
  have hjn : ∀ j, W'.sent (.join j) → W.sent (.join j) := by
    intro _ h
    rcases (hWs _).mp h with h | ⟨_, _, h⟩
    · exact h
    · cases h
  have hwon : ∀ a t, Won P W' a t → Won P W a t := by
    rintro a t ⟨he, hw | ⟨s, pt, pv, hs, hst⟩⟩
    · by_cases ha : a = n
      · subst ha; rw [hnode_n, e_ew, e_ct] at hw; exact ⟨he, Or.inl hw⟩
      · rw [hnode a ha] at hw; exact ⟨he, Or.inl hw⟩
    · exact ⟨he, Or.inr ⟨s, pt, pv, hpr _ _ _ _ hs, hst⟩⟩
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := ?_, join_term_le := ?_, join_unique := ?_,
      join_after_response := ?_, response_le := ?_, response_published := ?_, pub_wf := ?_, pub_parent := ?_,
      pub_unique := ?_, pub_rooted := ?_, pub_same_term := ?_, pub_voters := ?_, pub_election := ?_,
      commit_quorum := ?_, won_unique := ?_, pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_,
      leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ln]; exact hinv.localNode_eq m
    · rw [hnode m hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, hew]; intro h; cases h
    · rw [hnode m hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_sj]; exact hinv.won_started m
    · rw [hnode m hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, e_sj]; exact hinv.votes_started m
    · rw [hnode m hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_sj, e_ct]; exact hinv.started_term_pos m
    · rw [hnode m hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_jv, e_lcc, e_lac]; exact hinv.won_quorum m
    · rw [hnode m hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_jv, e_lcc, e_lac]; exact hinv.not_won_no_quorum m
    · rw [hnode m hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_jv, e_ct, e_lat, e_lav]
      intro hx
      obtain ⟨he, j, hj, h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j, hg _ hj, h1⟩
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, j, hj, h1⟩ := hinv.joinVotes_sent m x hx
      exact ⟨he, j, hg _ hj, h1⟩
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ct, e_lpv]
      intro hx
      obtain ⟨he, d, hd⟩ := hA x hx
      -- the responses counted by `m` are addressed to `m`
      rw [e_pv, addVote_mem] at hx
      rcases hx with hx | ⟨rfl, hxe⟩
      · obtain ⟨he', hs⟩ := hinv.publishVotes_sent m x hx
        exact ⟨he', hg _ hs⟩
      · refine ⟨hxe, hg _ ?_⟩
        have hr : r = ⟨(W.node m).currentTerm, (W.node m).lastPublishedVersion⟩ := by rw [← hrt, ← hrv]
        rw [← hr]
        exact hsent
    · rw [hnode m hm]
      intro hx
      obtain ⟨he, hs⟩ := hinv.publishVotes_sent m x hx
      exact ⟨he, hg _ hs⟩
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_ct]; exact hinv.term_le m hme
    · rw [hnode m hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_lat, e_lav, e_lcc, e_lac]
      exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
    · rw [hnode m hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j hj; exact hinv.join_wf j (hjn j hj)
  · intro j hj hje
    by_cases hm : j.sourceNode.id = n
    · rw [hm, hnode_n, e_ct]; have := hinv.join_term_le j (hjn j hj) hje; rw [hm] at this; exact this
    · rw [hnode _ hm]; exact hinv.join_term_le j (hjn j hj) hje
  · intro j j' hj hj'; exact hinv.join_unique j j' (hjn j hj) (hjn j' hj')
  · intro j a d r hj hr; exact hinv.join_after_response j a d r (hjn j hj) (hrs a d r hr)
  · intro a d r hr ha
    by_cases hm : a = n
    · subst hm; rw [hnode_n, e_ct, e_lat, e_lav]; exact hinv.response_le a d r (hrs a d r hr) ha
    · rw [hnode a hm]; exact hinv.response_le a d r (hrs a d r hr) ha
  · intro a d r hr
    obtain ⟨s, pt, pv, hs, h1, h2⟩ := hinv.response_published a d r (hrs a d r hr)
    exact ⟨s, pt, pv, hg _ hs, h1, h2⟩
  · intro src s pt pv hs; exact hinv.pub_wf src s pt pv (hpr _ _ _ _ hs)
  · intro src s pt pv hs hpt
    obtain ⟨src', s', pt', pv', hs', h1, h2, h3, h4⟩ := hinv.pub_parent src s pt pv (hpr _ _ _ _ hs) hpt
    exact ⟨src', s', pt', pv', hg _ hs', h1, h2, h3.imp id (fun h => ⟨h.1, committed_mono hg h.2⟩), h4⟩
  · intro src s pt pv src' s' pt' pv' hs hs'
    exact hinv.pub_unique src s pt pv src' s' pt' pv' (hpr _ _ _ _ hs) (hpr _ _ _ _ hs')
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv (hpr _ _ _ _ hs)
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' (hpr _ _ _ _ hs) (hpr _ _ _ _ hs') ht).imp
      (descends_mono hg) (descends_mono hg)
  · intro src s pt pv hs
    obtain ⟨J, h1, h2, h3⟩ := hinv.pub_voters src s pt pv (hpr _ _ _ _ hs)
    exact ⟨J, joinVoters_mono hg h1, h2, h3⟩
  · intro src s pt pv hs hpt
    obtain ⟨y, J, h1⟩ := hinv.pub_election src s pt pv (hpr _ _ _ _ hs) hpt
    exact ⟨y, J, electionRecord_mono hg h1⟩
  · intro c hc'
    have hrec : ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ s.term = c.term ∧
        s.version = c.version ∧ ∃ A, RespVoters P W c.term c.version A ∧
          s.lastAcceptedConfiguration.hasQuorum A = true ∧
          (s.lastCommittedConfiguration.hasQuorum A = true ∨
            (Committed W pt pv ∧ ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ s'.term = pt ∧
              s'.version = pv ∧ s'.lastAcceptedConfiguration = s.lastAcceptedConfiguration)) := by
      rcases (hWs _).mp hc' with h | ⟨c', hco, hx⟩
      · exact hinv.commit_quorum c h
      · cases hx; exact hC1 c hco
    obtain ⟨src, s, pt, pv, hs, h1, h2, A, hA', h3, h4⟩ := hrec
    refine ⟨src, s, pt, pv, hg _ hs, h1, h2, A, respVoters_mono hg hA', h3, ?_⟩
    rcases h4 with h4 | ⟨h4, src', s', pt', pv', hs', h5, h6, h7⟩
    · exact Or.inl h4
    · exact Or.inr ⟨committed_mono hg h4, src', s', pt', pv', hg _ hs', h5, h6, h7⟩
  · intro a b t ha hb
    exact hinv.won_unique a b t (hwon a t ha) (hwon b t hb)
  · intro src s pt pv hs
    have hs0 := hpr _ _ _ _ hs
    by_cases hm : src = n
    · subst hm; rw [hnode_n, e_ct, e_ew, e_sj]; exact hinv.pub_source_term src s pt pv hs0
    · rw [hnode src hm]; exact hinv.pub_source_term src s pt pv hs0
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_ct, e_lpv, e_jv]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv (hpr _ _ _ _ hs) ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
    · rw [hnode m hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv (hpr _ _ _ _ hs) ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lcc, e_lac]
      intro hw hne'
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne'
      exact ⟨s, hg _ hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
    · rw [hnode m hm]
      intro hw hne'
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne'
      exact ⟨s, hg _ hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [hnode_n, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lac]
      intro hw hv
      rcases hinv.leader_settled m hw hv with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun src s pt pv hs => h2 src s pt pv (hpr _ _ _ _ hs)⟩
    · rw [hnode m hm]
      intro hw hv
      rcases hinv.leader_settled m hw hv with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun src s pt pv hs => h2 src s pt pv (hpr _ _ _ _ hs)⟩

/-- `commit` preserves the invariant. -/
theorem OpenSearchSafety.inv_commit {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (c : ApplyCommitRequest) (cs' : CoordinationState V) (hsent : W.sent (.applyCommit c))
    (h : (W.node n).handleCommit c = .ok cs') : Inv P (W.set n cs') := by
  obtain ⟨hct, hlat, hlav, hcs⟩ := spec_commit _ _ _ h
  obtain ⟨mt, mv, mlac, mlcc⟩ := markCommitted_spec (W.node n).lastAcceptedState
  have e_ln : cs'.localNode = (W.node n).localNode := by rw [hcs]
  have e_ct : cs'.currentTerm = (W.node n).currentTerm := by rw [hcs]
  have e_ew : cs'.electionWon = (W.node n).electionWon := by rw [hcs]
  have e_jv : cs'.joinVotes = (W.node n).joinVotes := by rw [hcs]
  have e_pv : cs'.publishVotes = (W.node n).publishVotes := by rw [hcs]
  have e_sj : cs'.startedJoinSinceLastReboot = (W.node n).startedJoinSinceLastReboot := by rw [hcs]
  have e_lpv : cs'.lastPublishedVersion = (W.node n).lastPublishedVersion := by rw [hcs]
  have e_lpc : cs'.lastPublishedConfiguration = (W.node n).lastPublishedConfiguration := by rw [hcs]
  have e_lat : cs'.lastAcceptedTerm = (W.node n).lastAcceptedTerm := by rw [hcs]; exact mt
  have e_lav : cs'.lastAcceptedVersion = (W.node n).lastAcceptedVersion := by rw [hcs]; exact mv
  have e_lac : cs'.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; exact mlac
  have e_lcc : cs'.lastCommittedConfiguration = (W.node n).lastAcceptedConfiguration := by rw [hcs]; exact mlcc
  clear hcs h mt mv mlac mlcc
  have hg : ∀ m, W.sent m → (W.set n cs').sent m := fun _ h => h
  -- the accepted state is committed, hence of a term ≥ 1
  have hcomm : Committed W (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion := by
    rw [← hlat, ← hlav]; exact ⟨c.sourceNode, hsent⟩
  have hpos : 1 ≤ (W.node n).lastAcceptedTerm := (inv_committed_published P W hinv _ _ hcomm).1
  -- an eligible node's accepted state is the key of a publication with the same last accepted configuration
  have hQ : P.eligible n = true → ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧
      s.term = (W.node n).lastAcceptedTerm ∧ s.version = (W.node n).lastAcceptedVersion ∧
      (W.node n).lastAcceptedConfiguration = s.lastAcceptedConfiguration ∧
      ((W.node n).lastCommittedConfiguration = s.lastCommittedConfiguration ∨
        ((W.node n).lastCommittedConfiguration = s.lastAcceptedConfiguration ∧
          Committed W (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion)) := by
    intro hne
    rcases hinv.accepted_realizes n hne with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨src, s, pt, pv, hs, h1, h2, h3, h4⟩
    · omega
    · omega
    · exact ⟨src, s, pt, pv, hs, h1, h2, h3, h4⟩
  -- a node that has not won holds no quorum of its last accepted configuration (its term's publication is
  -- someone else's, whose voters are a quorum of that configuration)
  have hnoq : (W.node n).electionWon = false →
      (W.node n).joinVotes.isQuorum (W.node n).lastAcceptedConfiguration = true → False := by
    intro hew hq
    have hne0 : (W.node n).joinVotes.nodes ≠ [] := ne_nil_of_hasQuorum _ _ hq
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne0
    obtain ⟨-, j, hj, -, htgt, -⟩ := hinv.joinVotes_sent n m hm
    have hne : P.eligible n = true := by have := (hinv.join_wf j hj).2; rwa [htgt] at this
    obtain ⟨L, s, pt, pv, hs, h1, -, h3, -⟩ := hQ hne
    obtain ⟨J, hJ, -, hJq⟩ := hinv.pub_voters L s pt pv hs
    have hq' : s.lastAcceptedConfiguration.hasQuorum (W.node n).joinVotes.nodes = true := by rw [← h3]; exact hq
    obtain ⟨x, -, hx1, hx2⟩ := quorum_intersect _ _ _ hq' hJq
    obtain ⟨hxe, j₁, hj₁, hs₁, ht₁, hterm₁, -⟩ := hinv.joinVotes_sent n x hx1
    obtain ⟨-, j₂, hj₂, hs₂, ht₂, hterm₂⟩ := hJ x hx2
    have hjj := hinv.join_unique j₁ j₂ hj₁ hj₂ (by rw [hs₁]; exact hxe) (hs₁.trans hs₂.symm)
      (by rw [hterm₁, hterm₂, h1, ← hlat, hct])
    have hLn : L = n := by rw [← ht₂, ← hjj, ht₁]
    subst hLn
    rcases hinv.pub_source_term L s pt pv hs with hlt | ⟨-, hw | hsj⟩
    · rw [h1, ← hlat, hct] at hlt; omega
    · rw [hw] at hew; cases hew
    · rw [hinv.votes_started L hne0] at hsj; cases hsj
  have hwon : ∀ a t, Won P (W.set n cs') a t → Won P W a t := by
    rintro a t ⟨he, hw | hp⟩
    · by_cases ha : a = n
      · subst ha; rw [set_node_self, e_ew, e_ct] at hw; exact ⟨he, Or.inl hw⟩
      · rw [set_node_ne _ _ _ _ ha] at hw; exact ⟨he, Or.inl hw⟩
    · exact ⟨he, Or.inr hp⟩
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := hinv.join_wf, join_term_le := ?_, join_unique := hinv.join_unique,
      join_after_response := hinv.join_after_response, response_le := ?_,
      response_published := hinv.response_published, pub_wf := hinv.pub_wf, pub_parent := hinv.pub_parent,
      pub_unique := hinv.pub_unique, pub_rooted := ?_, pub_same_term := ?_, pub_voters := hinv.pub_voters,
      pub_election := hinv.pub_election, commit_quorum := hinv.commit_quorum, won_unique := ?_,
      pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_, leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ln]; exact hinv.localNode_eq m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_pv]; exact hinv.idle_of_not_won m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_sj]; exact hinv.won_started m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv, e_sj]; exact hinv.votes_started m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj, e_ct]; exact hinv.started_term_pos m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_jv, e_lcc, e_lac]
      intro hw
      have := (hinv.won_quorum m hw).2
      exact ⟨this, this⟩
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_jv, e_lcc, e_lac]
      intro hew hq
      exact hnoq hew hq.1
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv, e_ct, e_lat, e_lav]; exact hinv.joinVotes_sent m x
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.joinVotes_sent m x
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_pv, e_ct, e_lpv]; exact hinv.publishVotes_sent m x
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.publishVotes_sent m x
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lat, e_ct]; exact hinv.term_le m hme
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lat, e_lav, e_lcc, e_lac]
      obtain ⟨src, s, pt, pv, hs, h1, h2, h3, -⟩ := hQ hme
      exact Or.inr (Or.inr ⟨src, s, pt, pv, hs, h1, h2, h3, Or.inr ⟨h3, hcomm⟩⟩)
    · rw [set_node_ne _ _ _ _ hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j hj hje
    by_cases hm : j.sourceNode.id = n
    · rw [hm, set_node_self, e_ct]; have := hinv.join_term_le j hj hje; rw [hm] at this; exact this
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.join_term_le j hj hje
  · intro a d r hr ha
    by_cases hm : a = n
    · subst hm; rw [set_node_self, e_ct, e_lat, e_lav]; exact hinv.response_le a d r hr ha
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.response_le a d r hr ha
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv hs
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' hs hs' ht).imp (descends_mono hg) (descends_mono hg)
  · intro a b t ha hb
    exact hinv.won_unique a b t (hwon a t ha) (hwon b t hb)
  · intro src s pt pv hs
    by_cases hm : src = n
    · subst hm; rw [set_node_self, e_ct, e_ew, e_sj]; exact hinv.pub_source_term src s pt pv hs
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.pub_source_term src s pt pv hs
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_ct, e_lpv, e_jv]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv hs ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
    · rw [set_node_ne _ _ _ _ hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv hs ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · -- D1: the leader applies the commit of its accepted state while its next publication is in flight
      subst hm; rw [set_node_self, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lcc, e_lac]
      intro hw hne
      obtain ⟨C, hC, h1, h2, h3, -⟩ := hinv.leader_inflight m hw hne
      refine ⟨C, hC, h1, h2, h3, ?_⟩
      have hme := inv_eligible_of_won P W hinv m hw
      obtain ⟨src, s, pt, pv, hs, hs1, hs2, hs3, -⟩ := hQ hme
      obtain ⟨src', s', pt', pv', hs', hs'1, hs'2, -, hR2⟩ := hinv.pub_parent m C _ _ hC hpos
      obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique src s pt pv src' s' pt' pv' hs hs' (hs1.trans hs'1.symm)
        (hs2.trans hs'2.symm)
      by_cases hac : C.lastAcceptedConfiguration = s.lastAcceptedConfiguration
      · exact Or.inr ⟨by rw [hs3, hac], committed_mono hg hcomm, by rw [hs3, hac]⟩
      · exact Or.inl (by rw [hs3, hR2 hac])
    · rw [set_node_ne _ _ _ _ hm]
      intro hw hne
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne
      exact ⟨s, hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew, e_lpv, e_lav, e_lat, e_ct, e_lpc, e_lac]
      intro hw hv
      rcases hinv.leader_settled m hw hv with h | ⟨hlt, -⟩
      · exact Or.inl h
      · rw [← hlat, hct] at hlt; omega
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.leader_settled m

/-- `restart` (of a cluster-manager-eligible node) preserves the invariant. -/
theorem OpenSearchSafety.inv_restart {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (s' : ClusterState V) (hn : P.eligible n = true)
    (hs : RestartState (W.node n).lastAcceptedState s') :
    Inv P (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s')) := by
  generalize hcs : CoordinationState.init (W.node n).localNode (W.node n).currentTerm s' = cs₁
  have e_ln : cs₁.localNode = (W.node n).localNode := by rw [← hcs]; rfl
  have e_ct : cs₁.currentTerm = (W.node n).currentTerm := by rw [← hcs]; rfl
  have e_ew : cs₁.electionWon = false := by rw [← hcs]; rfl
  have e_jv : cs₁.joinVotes = VoteCollection.empty := by rw [← hcs]; rfl
  have e_pv : cs₁.publishVotes = VoteCollection.empty := by rw [← hcs]; rfl
  have e_sj : cs₁.startedJoinSinceLastReboot = false := by rw [← hcs]; rfl
  have e_lpv : cs₁.lastPublishedVersion = 0 := by rw [← hcs]; rfl
  -- the persisted key and configurations are kept, or the node never joined a cluster
  have hkey : (cs₁.lastAcceptedTerm = (W.node n).lastAcceptedTerm ∧
      cs₁.lastAcceptedVersion = (W.node n).lastAcceptedVersion ∧
      cs₁.lastCommittedConfiguration = (W.node n).lastCommittedConfiguration ∧
      cs₁.lastAcceptedConfiguration = (W.node n).lastAcceptedConfiguration) ∨
      ((W.node n).lastAcceptedTerm = 0 ∧ cs₁.lastAcceptedTerm = 0 ∧
        cs₁.lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∧
        cs₁.lastAcceptedConfiguration = VotingConfiguration.EMPTY_CONFIG) := by
    subst hcs
    rcases hs with ⟨h1, h2, h3, h4, -⟩ | ⟨h1, -, -, -, h5, h6, h7⟩
    · exact Or.inl ⟨h1, h2, h3, h4⟩
    · exact Or.inr ⟨h1, h5, h6, h7⟩
  have hg : ∀ m, W.sent m → (W.set n cs₁).sent m := fun _ h => h
  -- winning only shrinks
  have hwon : ∀ a t, Won P (W.set n cs₁) a t → Won P W a t := by
    rintro a t ⟨he, hw | hp⟩
    · by_cases ha : a = n
      · subst ha; rw [set_node_self, e_ew] at hw; cases hw.1
      · rw [set_node_ne _ _ _ _ ha] at hw; exact ⟨he, Or.inl hw⟩
    · exact ⟨he, Or.inr hp⟩
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := hinv.join_wf, join_term_le := ?_, join_unique := hinv.join_unique,
      join_after_response := hinv.join_after_response, response_le := ?_,
      response_published := hinv.response_published, pub_wf := hinv.pub_wf, pub_parent := hinv.pub_parent,
      pub_unique := hinv.pub_unique, pub_rooted := ?_, pub_same_term := ?_, pub_voters := hinv.pub_voters,
      pub_election := hinv.pub_election, commit_quorum := hinv.commit_quorum, won_unique := ?_,
      pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_, leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ln]; exact hinv.localNode_eq m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lpv, e_pv]; intro _; exact ⟨rfl, rfl⟩
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv]; intro h; exact absurd rfl h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv, isQuorum_empty]; intro _ h; cases h.1
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.joinVotes_sent m x
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_pv]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.publishVotes_sent m x
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ct]
      rcases hkey with ⟨k1, -⟩ | ⟨-, k1, -⟩
      · rw [k1]; exact hinv.term_le m hme
      · rw [k1]; exact Nat.zero_le _
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.term_le m hme
  · intro m hme
    by_cases hm : m = n
    · subst hm; rw [set_node_self]
      rcases hkey with ⟨k1, k2, k3, k4⟩ | ⟨-, k1, k2, k3⟩
      · rw [k1, k2, k3, k4]
        exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
      · exact Or.inl ⟨k1, k2, k3⟩
    · rw [set_node_ne _ _ _ _ hm]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j hj hje
    by_cases hm : j.sourceNode.id = n
    · rw [hm, set_node_self, e_ct]; have := hinv.join_term_le j hj hje; rw [hm] at this; exact this
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.join_term_le j hj hje
  · intro a d r hr ha
    by_cases hm : a = n
    · subst hm; rw [set_node_self, e_ct]
      obtain ⟨h1, h2⟩ := hinv.response_le a d r hr ha
      refine ⟨h1, ?_⟩
      rcases hkey with ⟨k1, k2, -, -⟩ | ⟨k0, k1, -, -⟩
      · rw [k1, k2]; exact h2
      · -- a node that never accepted a publication sent no response
        obtain ⟨s, pt, pv, hs, hst, -⟩ := hinv.response_published a d r hr
        have := (hinv.pub_wf _ _ _ _ hs).2.1
        unfold KeyLE at h2
        rw [k0] at h2
        omega
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.response_le a d r hr ha
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv hs
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' hs hs' ht).imp (descends_mono hg) (descends_mono hg)
  · intro a b t ha hb
    exact hinv.won_unique a b t (hwon a t ha) (hwon b t hb)
  · intro src s pt pv hs
    by_cases hm : src = n
    · subst hm; rw [set_node_self, e_ct, e_sj]
      rcases hinv.pub_source_term src s pt pv hs with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, Or.inr rfl⟩
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.pub_source_term src s pt pv hs
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv hs ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]
      intro hw hne
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne
      exact ⟨s, hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.leader_settled m

/-- `restartAny` (of a node that is not cluster-manager-eligible) preserves the invariant. -/
theorem OpenSearchSafety.inv_restartAny {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (t : Nat) (s' : ClusterState V) (hn : P.eligible n = false) :
    Inv P (W.set n (CoordinationState.init (W.node n).localNode t s')) := by
  generalize hcs : CoordinationState.init (W.node n).localNode t s' = cs₁
  have e_ln : cs₁.localNode = (W.node n).localNode := by rw [← hcs]; rfl
  have e_ew : cs₁.electionWon = false := by rw [← hcs]; rfl
  have e_jv : cs₁.joinVotes = VoteCollection.empty := by rw [← hcs]; rfl
  have e_pv : cs₁.publishVotes = VoteCollection.empty := by rw [← hcs]; rfl
  have e_sj : cs₁.startedJoinSinceLastReboot = false := by rw [← hcs]; rfl
  have e_lpv : cs₁.lastPublishedVersion = 0 := by rw [← hcs]; rfl
  have hne : ∀ m, P.eligible m = true → m ≠ n := by
    rintro m hm rfl; rw [hn] at hm; cases hm
  have hg : ∀ m, W.sent m → (W.set n cs₁).sent m := fun _ h => h
  have hwon : ∀ a t, Won P (W.set n cs₁) a t → Won P W a t := by
    rintro a t ⟨he, hw | hp⟩
    · rw [set_node_ne _ _ _ _ (hne a he)] at hw; exact ⟨he, Or.inl hw⟩
    · exact ⟨he, Or.inr hp⟩
  refine
    { localNode_eq := ?_, idle_of_not_won := ?_, won_started := ?_, votes_started := ?_, started_term_pos := ?_,
      won_quorum := ?_, not_won_no_quorum := ?_, joinVotes_sent := ?_, publishVotes_sent := ?_, term_le := ?_,
      accepted_realizes := ?_, join_wf := hinv.join_wf, join_term_le := ?_, join_unique := hinv.join_unique,
      join_after_response := hinv.join_after_response, response_le := ?_,
      response_published := hinv.response_published, pub_wf := hinv.pub_wf, pub_parent := hinv.pub_parent,
      pub_unique := hinv.pub_unique, pub_rooted := ?_, pub_same_term := ?_, pub_voters := hinv.pub_voters,
      pub_election := hinv.pub_election, commit_quorum := hinv.commit_quorum, won_unique := ?_,
      pub_source_term := ?_, leader_pubs := ?_, leader_inflight := ?_, leader_settled := ?_ }
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ln]; exact hinv.localNode_eq m
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.localNode_eq m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_lpv, e_pv]; intro _; exact ⟨rfl, rfl⟩
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.idle_of_not_won m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv]; intro h; exact absurd rfl h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.votes_started m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_sj]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.started_term_pos m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.won_quorum m
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv, isQuorum_empty]; intro _ h; cases h.1
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.not_won_no_quorum m
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_jv]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.joinVotes_sent m x
  · intro m x
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_pv]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.publishVotes_sent m x
  · intro m hme
    rw [set_node_ne _ _ _ _ (hne m hme)]; exact hinv.term_le m hme
  · intro m hme
    rw [set_node_ne _ _ _ _ (hne m hme)]; exact (hinv.accepted_realizes m hme).imp id (realizes_mono hg)
  · intro j hj hje
    rw [set_node_ne _ _ _ _ (hne _ hje)]; exact hinv.join_term_le j hj hje
  · intro a d r hr ha
    rw [set_node_ne _ _ _ _ (hne a ha)]; exact hinv.response_le a d r hr ha
  · intro src s pt pv hs
    obtain ⟨v₀, h⟩ := hinv.pub_rooted src s pt pv hs
    exact ⟨v₀, descends_mono hg h⟩
  · intro src s pt pv src' s' pt' pv' hs hs' ht
    exact (hinv.pub_same_term src s pt pv src' s' pt' pv' hs hs' ht).imp (descends_mono hg) (descends_mono hg)
  · intro a b t ha hb
    exact hinv.won_unique a b t (hwon a t ha) (hwon b t hb)
  · intro src s pt pv hs
    rw [set_node_ne _ _ _ _ (hne src (hinv.pub_wf src s pt pv hs).1)]; exact hinv.pub_source_term src s pt pv hs
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]
      intro hw src s pt pv hs ht
      obtain ⟨h1, h2, h3, h4⟩ := hinv.leader_pubs m hw src s pt pv hs ht
      exact ⟨h1, descends_mono hg h2, h3, h4⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]
      intro hw hne
      obtain ⟨s, hs, h1, h2, h3, h4⟩ := hinv.leader_inflight m hw hne
      exact ⟨s, hs, h1, h2, h3, h4.imp id (fun h => ⟨h.1, committed_mono hg h.2.1, h.2.2⟩)⟩
  · intro m
    by_cases hm : m = n
    · subst hm; rw [set_node_self, e_ew]; intro h; cases h
    · rw [set_node_ne _ _ _ _ hm]; exact hinv.leader_settled m
