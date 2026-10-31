import Definitions.Def_OpenSearchSafety
import Theorems.Thm_OpenSearchSafety_inv_init
import Theorems.Thm_OpenSearchSafety_inv_bootstrap
import Theorems.Thm_OpenSearchSafety_inv_startJoin
import Theorems.Thm_OpenSearchSafety_inv_join
import Theorems.Thm_OpenSearchSafety_inv_clientValue
import Theorems.Thm_OpenSearchSafety_inv_publish
import Theorems.Thm_OpenSearchSafety_inv_respond
import Theorems.Thm_OpenSearchSafety_inv_commit
import Theorems.Thm_OpenSearchSafety_inv_restart
import Theorems.Thm_OpenSearchSafety_inv_restartAny
import Theorems.Thm_OpenSearchSafety_inv_descends_key
import Theorems.Thm_OpenSearchSafety_inv_committed_published
import Theorems.Thm_OpenSearchSafety_inv_won_of_electionWon
import Theorems.Thm_OpenSearchSafety_inv_pub_lcc
import Theorems.Thm_OpenSearchSafety_inv_leader_completeness
import Theorems.Thm_OpenSearchSafety_inv_committed_comparable

open OpenSearchCoordination OpenSearchSafety

/-! # OpenSearch cluster coordination: safety

Public statements of the safety mission. Hypotheses common to all: the bootstrap configurations are compatible
(`P.InitCompatible`, which `bootstrap_compatible` proves for the configurations `ClusterBootstrapService` builds) and
the election strategy is OpenSearch's default (a non-monotone plugin strategy breaks safety; see the notes).

Every reachable cluster satisfies the invariant `Inv` (`reachable_inv`, by induction over `Reachable`, with one
preservation result per step); the safety properties are consequences of `Inv` inside one cluster. `commit_reachable`
shows that the hypotheses are satisfiable and that commits do happen. -/

/-- **The invariant holds in every reachable cluster.** -/
theorem OpenSearchSafety.reachable_inv {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W) : Inv P W := by
  induction hW with
  | init W h => exact inv_init P W h
  | step W W' _ hs ih =>
    cases hs with
    | bootstrap n X s cs' hX hcontract hconf h =>
      exact inv_bootstrap P hP hes W ih n X s cs' hX hcontract hconf h
    | startJoin n src t cs' j hsrc h => exact inv_startJoin P hP hes W ih n src t cs' j hsrc h
    | join n j cs' b hsent hdest h => exact inv_join P hP hes W ih n j cs' b hsent hdest h
    | clientValue n s cs' p hcontract h => exact inv_clientValue P hP hes W ih n s cs' p hcontract h
    | publish n src s pt pv cs' r hsent h => exact inv_publish P hP hes W ih n src s pt pv cs' r hsent h
    | respond n src r cs' o hsent h =>
      cases o with
      | none => exact inv_respond P hP hes W ih n src r cs' none hsent h
      | some c => exact inv_respond P hP hes W ih n src r cs' (some c) hsent h
    | commit n c cs' hsent h => exact inv_commit P hP hes W ih n c cs' hsent h
    | restart n s' hn hs => exact inv_restart P hP hes W ih n s' hn hs
    | restartAny n t s' hn => exact inv_restartAny P hP hes W ih n t s' hn

/-- **One cluster-manager per term.** Two publications of the same term come from the same node. (OpenSearch's
randomized `CoordinationStateTestCluster.invariant()` checks this on random executions.) -/
theorem OpenSearchSafety.one_master_per_term {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (s s' : ClusterState V) (pt pt' : Nat) (pv pv' : Int)
    (h₁ : W.sent (.publishRequest a s pt pv)) (h₂ : W.sent (.publishRequest b s' pt' pv'))
    (ht : s.term = s'.term) : a = b := by
  have hinv := reachable_inv P hP hes W hW
  exact hinv.won_unique a b s.term ⟨(hinv.pub_wf _ _ _ _ h₁).1, Or.inr ⟨s, pt, pv, h₁, rfl⟩⟩
    ⟨(hinv.pub_wf _ _ _ _ h₂).1, Or.inr ⟨s', pt', pv', h₂, ht.symm⟩⟩

/-- **One cluster state per term and version.** Two publications with the same term and version are the same
publication: same publisher, same cluster state, same parent. (Also checked by `CoordinationStateTestCluster`.) -/
theorem OpenSearchSafety.one_state_per_version {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (s s' : ClusterState V) (pt pt' : Nat) (pv pv' : Int)
    (h₁ : W.sent (.publishRequest a s pt pv)) (h₂ : W.sent (.publishRequest b s' pt' pv'))
    (ht : s.term = s'.term) (hv : s.version = s'.version) : a = b ∧ s = s' ∧ pt = pt' ∧ pv = pv' := by
  exact (reachable_inv P hP hes W hW).pub_unique _ _ _ _ _ _ _ _ h₁ h₂ ht hv

/-- **Leader completeness.** Every publication of a later term descends from every committed publication: a
cluster-manager elected after a commit always builds on the committed state. -/
theorem OpenSearchSafety.leader_completeness {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (t : Nat) (v : Int) (hc : Committed W t v) (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
    (hs : W.sent (.publishRequest src s pt pv)) (hlt : t < s.term) :
    Descends W t v s.term s.version := by
  exact inv_leader_completeness P hP W (reachable_inv P hP hes W hW) t v hc src s pt pv hs hlt

/-- **Committed states never fork.** Any two committed publications are related by descent: the committed cluster
states form a single history. -/
theorem OpenSearchSafety.committed_linear {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (t₁ t₂ : Nat) (v₁ v₂ : Int) (h₁ : Committed W t₁ v₁) (h₂ : Committed W t₂ v₂) :
    Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
  exact inv_committed_comparable P hP W (reachable_inv P hP hes W hW) t₁ t₂ v₁ v₂ h₁ h₂

/-- **A committed version is committed once.** Two committed publications with the same version have the same term
(hence, by `one_state_per_version`, they are the same publication with the same cluster state); and committed versions
increase with the term. -/
theorem OpenSearchSafety.committed_versions {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (t₁ t₂ : Nat) (v₁ v₂ : Int) (h₁ : Committed W t₁ v₁) (h₂ : Committed W t₂ v₂) :
    (v₁ = v₂ → t₁ = t₂) ∧ (t₁ < t₂ → v₁ < v₂) := by
  have hinv := reachable_inv P hP hes W hW
  constructor
  · intro hv
    rcases inv_committed_comparable P hP W hinv t₁ t₂ v₁ v₂ h₁ h₂ with h | h
    · rcases inv_descends_key P W hinv _ _ _ _ h with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · omega
    · rcases inv_descends_key P W hinv _ _ _ _ h with ⟨h, -⟩ | ⟨-, h⟩
      · exact h.symm
      · omega
  · intro ht
    obtain ⟨-, src, s, pt, pv, hs, h1, h2⟩ := inv_committed_published P W hinv t₂ v₂ h₂
    have h := inv_leader_completeness P hP W hinv t₁ v₁ h₁ src s pt pv hs (by omega)
    rw [h1, h2] at h
    rcases inv_descends_key P W hinv _ _ _ _ h with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h

/-- Every commit is of a publication. -/
theorem OpenSearchSafety.committed_published {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (t : Nat) (v : Int) (h : Committed W t v) :
    ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ s.term = t ∧ s.version = v := by
  exact (inv_committed_published P W (reachable_inv P hP hes W hW) t v h).2

/-- **Election safety.** Two nodes that have both won the election of their current term, in the same term, are the
same node. -/
theorem OpenSearchSafety.election_safety {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (ha : (W.node a).electionWon = true) (hb : (W.node b).electionWon = true)
    (ht : (W.node a).currentTerm = (W.node b).currentTerm) : a = b := by
  have hinv := reachable_inv P hP hes W hW
  have hb' := inv_won_of_electionWon P W hinv b hb
  rw [← ht] at hb'
  exact hinv.won_unique a b _ (inv_won_of_electionWon P W hinv a ha) hb'

/-- **The assertions of `CoordinationState.invariant()` never fail.** At every cluster-manager-eligible node of every
reachable cluster, `invariant()` holds — although no handler preserves it on its own
(`OpenSearchCoordination.javaInvariant_not_local`). -/
theorem OpenSearchSafety.javaInvariant_reachable {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (n : NodeId) (hn : P.eligible n = true) : (W.node n).javaInvariant P.strategy := by
  have hinv := reachable_inv P hP hes W hW
  unfold CoordinationState.javaInvariant
  refine ⟨hinv.term_le n hn, ?_, ?_, hinv.won_started n, ?_⟩
  · rw [hes]
    unfold CoordinationState.isElectionQuorum
    cases hw : (W.node n).electionWon
    · have := hinv.not_won_no_quorum n hw
      simp only [ElectionStrategy.DEFAULT_INSTANCE, Bool.and_true]
      cases h1 : (W.node n).joinVotes.isQuorum (W.node n).lastCommittedConfiguration <;>
        cases h2 : (W.node n).joinVotes.isQuorum (W.node n).lastAcceptedConfiguration <;> simp_all
    · obtain ⟨h1, h2⟩ := hinv.won_quorum n hw
      simp [h1, h2, ElectionStrategy.DEFAULT_INSTANCE]
  · cases hw : (W.node n).electionWon
    · simpa using (hinv.idle_of_not_won n hw).1
    · simp only [if_true]
      by_cases he : (W.node n).lastPublishedVersion = (W.node n).lastAcceptedVersion
      · omega
      · obtain ⟨s, hs, -, hv, -⟩ := hinv.leader_inflight n hw he
        have := (hinv.pub_wf _ _ _ _ hs).2.2.2.1
        omega
  · cases hw : (W.node n).electionWon
    · left; rw [(hinv.idle_of_not_won n hw).2]; rfl
    · right; rfl

/-- **Committed configurations are committed.** The last committed configuration of every cluster-manager-eligible
node is empty (not bootstrapped), a bootstrap configuration, or the accepted configuration of a committed
publication. -/
theorem OpenSearchSafety.lastCommitted_committed {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (n : NodeId) (hn : P.eligible n = true) :
    (W.node n).lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG ∨
    P.initConfs (W.node n).lastCommittedConfiguration ∨
    ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ Committed W s.term s.version ∧
      s.lastAcceptedConfiguration = (W.node n).lastCommittedConfiguration := by
  have hinv := reachable_inv P hP hes W hW
  rcases hinv.accepted_realizes n hn with ⟨-, h0, -⟩ | ⟨-, -, hX⟩ |
      ⟨src, s, pt, pv, hs, h1, h2, -, h4 | ⟨h4, hc⟩⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl hX)
  · rcases inv_pub_lcc P W hinv src s pt pv hs with h | ⟨src', s', pt', pv', hs', hc', he⟩
    · rw [h4]; exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨src', s', pt', pv', hs', hc', he.trans h4.symm⟩)
  · exact Or.inr (Or.inr ⟨src, s, pt, pv, hs, by rw [h1, h2]; exact hc, h4.symm⟩)

/-- **Bootstrapping is safe even with different partial views.** The configurations `ClusterBootstrapService` builds
are compatible, whatever subset of the required nodes each bootstrapping node has discovered, provided each requirement
names the same node everywhere (`resolve` injective on the requirements), placeholders are distinct from each other
and from the named nodes, and placeholders are not cluster-manager-eligible node ids. -/
theorem OpenSearchSafety.bootstrap_compatible (eligible : NodeId → Bool) (k : Nat) (resolve placeholder : Nat → NodeId)
    (hres : ∀ i j, i < k → j < k → resolve i = resolve j → i = j)
    (hph : ∀ i j, i < k → j < k → placeholder i = placeholder j → i = j)
    (hdis : ∀ i j, i < k → j < k → placeholder i ≠ resolve j)
    (hphe : ∀ i, i < k → eligible (placeholder i) = false)
    (X Y : VotingConfiguration) (mX mY : Nat → Bool)
    (hX : BootstrapConfig k resolve placeholder mX X) (hY : BootstrapConfig k resolve placeholder mY Y)
    (q₁ q₂ : List NodeId) (hq₁ : ∀ x ∈ q₁, eligible x = true) (hq₂ : ∀ x ∈ q₂, eligible x = true)
    (h₁ : X.hasQuorum q₁ = true) (h₂ : Y.hasQuorum q₂ = true) : ∃ x, x ∈ q₁ ∧ x ∈ q₂ := by
  sorry

/-- **Commits happen.** Some cluster with a compatible bootstrap configuration and the default strategy reaches a
commit of term 1, version 1: the hypotheses of the safety theorems are satisfiable, and they are not vacuous. -/
theorem OpenSearchSafety.commit_reachable : ∃ (P : Params) (W : Cluster Unit), P.InitCompatible ∧
    P.strategy = ElectionStrategy.DEFAULT_INSTANCE ∧ Reachable P W ∧ Committed W 1 1 := by
  sorry
