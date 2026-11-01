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

/-- **Leader completeness.** Every publication of a later term than a committed publication descends from it: a
cluster-manager of a later term always builds on the committed state (publications of the committed key's own term or of
older terms are not covered). -/
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

/-- **Election safety.** Two nodes that hold a won election at the same moment (in the same cluster), in the same
current term, are the same node. -/
theorem OpenSearchSafety.election_safety {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hW : Reachable P W)
    (a b : NodeId) (ha : (W.node a).electionWon = true) (hb : (W.node b).electionWon = true)
    (ht : (W.node a).currentTerm = (W.node b).currentTerm) : a = b := by
  have hinv := reachable_inv P hP hes W hW
  have hb' := inv_won_of_electionWon P W hinv b hb
  rw [← ht] at hb'
  exact hinv.won_unique a b _ (inv_won_of_electionWon P W hinv a ha) hb'

/-- **The assertions of `CoordinationState.invariant()` never fail at a cluster-manager-eligible node.** At every
cluster-manager-eligible node of every reachable cluster, `invariant()` holds, although not every handler preserves it
on its own: `handlePublishRequest` can break it (`OpenSearchCoordination.javaInvariant_not_local`). -/
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

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
private theorem filter_length_add_le {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).length + (L.filter q).length ≤ L.length + (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    cases hp : p y <;> cases hq : q y <;> simp [hp, hq] <;> omega

/-- **Bootstrapping with different partial views gives compatible configurations.** Two configurations of the form
`ClusterBootstrapService` builds (`BootstrapConfig`, with the same requirements, `resolve` and `placeholder`) meet the
condition of `Params.InitCompatible`, whatever subset of the required nodes each bootstrapping node has discovered,
provided each requirement names its own node, the same everywhere (`resolve` injective on the requirements),
placeholders are distinct from each other and from the named nodes, and placeholders are not cluster-manager-eligible
node ids. `Params` is not mentioned: that the model's bootstrap configurations have this form is not formalized. -/
theorem OpenSearchSafety.bootstrap_compatible (eligible : NodeId → Bool) (k : Nat) (resolve placeholder : Nat → NodeId)
    (hres : ∀ i j, i < k → j < k → resolve i = resolve j → i = j)
    (hph : ∀ i j, i < k → j < k → placeholder i = placeholder j → i = j)
    (hdis : ∀ i j, i < k → j < k → placeholder i ≠ resolve j)
    (hphe : ∀ i, i < k → eligible (placeholder i) = false)
    (X Y : VotingConfiguration) (mX mY : Nat → Bool)
    (hX : BootstrapConfig k resolve placeholder mX X) (hY : BootstrapConfig k resolve placeholder mY Y)
    (q₁ q₂ : List NodeId) (hq₁ : ∀ x ∈ q₁, eligible x = true) (hq₂ : ∀ x ∈ q₂, eligible x = true)
    (h₁ : X.hasQuorum q₁ = true) (h₂ : Y.hasQuorum q₂ = true) : ∃ x, x ∈ q₁ ∧ x ∈ q₂ := by
  -- an eligible quorum of a bootstrap configuration names more than half of the requirements, all matched
  have key : ∀ (m : Nat → Bool) (Z : VotingConfiguration) (q : List NodeId),
      BootstrapConfig k resolve placeholder m Z → (∀ x ∈ q, eligible x = true) → Z.hasQuorum q = true →
      ((List.range k).filter (fun i => m i && q.contains (resolve i))).length * 2 > k := by
    intro m Z q hZ hq hQ
    have hinj : ∀ i j, i < k → j < k → (if m i then resolve i else placeholder i) =
        (if m j then resolve j else placeholder j) → i = j := by
      intro i j hi hj he
      cases hmi : m i <;> cases hmj : m j <;> simp only [hmi, hmj, if_true, if_false,
        Bool.false_eq_true] at he
      · exact hph i j hi hj he
      · exact absurd he (hdis i j hi hj)
      · exact absurd he.symm (hdis j i hj hi)
      · exact hres i j hi hj he
    have hnodupZ : Z.nodeIds.Nodup := Z.sorted.imp (fun h => Nat.ne_of_lt h)
    -- the configuration has at least `k` members
    have hL : ((List.range k).map (fun i => if m i then resolve i else placeholder i)).Nodup := by
      rw [List.Nodup, List.pairwise_map]
      exact List.nodup_range.imp_of_mem
        (fun ha hb hab he => hab (hinj _ _ (List.mem_range.mp ha) (List.mem_range.mp hb) he))
    have hsub1 : (List.range k).map (fun i => if m i then resolve i else placeholder i) ⊆ Z.nodeIds := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact (hZ.1 _).mpr ⟨i, List.mem_range.mp hi, rfl⟩
    have hk : k ≤ Z.nodeIds.length := by
      have := List.Nodup.length_le_of_subset hL hsub1
      simpa using this
    -- its members in the quorum are the matched requirements named in the quorum
    have hsub2 : Z.nodeIds.filter (fun x => q.contains x) ⊆
        ((List.range k).filter (fun i => m i && q.contains (resolve i))).map resolve := by
      intro x hx
      rw [List.mem_filter, List.contains_iff_mem] at hx
      obtain ⟨i, hi, rfl⟩ := (hZ.1 _).mp hx.1
      have hxq := hx.2
      cases hmi : m i
      · simp only [hmi, if_false, Bool.false_eq_true] at hxq
        have := hq _ hxq
        rw [hphe i hi] at this
        cases this
      · simp only [hmi, if_true] at hxq ⊢
        exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi, by simp [hmi, hxq]⟩, rfl⟩
    have hle := List.Nodup.length_le_of_subset (hnodupZ.sublist List.filter_sublist) hsub2
    rw [List.length_map] at hle
    simp only [VotingConfiguration.hasQuorum, decide_eq_true_eq] at hQ
    omega
  have hA := key mX X q₁ hX hq₁ h₁
  have hB := key mY Y q₂ hY hq₂ h₂
  have hc := filter_length_add_le (List.range k) (fun i => mX i && q₁.contains (resolve i))
    (fun i => mY i && q₂.contains (resolve i))
  rw [List.length_range] at hc
  have hpos : 0 < ((List.range k).filter
      (fun i => (mX i && q₁.contains (resolve i)) && (mY i && q₂.contains (resolve i)))).length := by
    omega
  obtain ⟨i, hi⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, Bool.and_eq_true, List.contains_iff_mem] at hi
  exact ⟨resolve i, hi.2.1.2, hi.2.2.2⟩

/-- **Commits happen.** Some cluster with a compatible bootstrap configuration and the default strategy reaches a
commit of term 1, version 1: the hypotheses common to the safety theorems can be met together with a commit. Only this
one committed key is exhibited, not two distinct committed keys or a publication of a later term than a committed
key. -/
theorem OpenSearchSafety.commit_reachable : ∃ (P : Params) (W : Cluster Unit), P.InitCompatible ∧
    P.strategy = ElectionStrategy.DEFAULT_INSTANCE ∧ Reachable P W ∧ Committed W 1 1 := by
  -- one cluster-manager-eligible node, 0, bootstrapping alone
  let X₀ : VotingConfiguration := ⟨[0], List.Pairwise.cons (fun _ h => by cases h) .nil⟩
  let P : Params := ⟨fun _ => true, fun X => X = X₀, ElectionStrategy.DEFAULT_INSTANCE⟩
  have hP : P.InitCompatible := by
    intro X Y hX hY q₁ q₂ _ _ h₁ h₂
    have hX' : X = X₀ := hX
    have hY' : Y = X₀ := hY
    subst hX' hY'
    have m₁ : (0 : NodeId) ∈ q₁ := by
      by_cases hc : (0 : NodeId) ∈ q₁
      · exact hc
      · simp [VotingConfiguration.hasQuorum, X₀, hc] at h₁
    have m₂ : (0 : NodeId) ∈ q₂ := by
      by_cases hc : (0 : NodeId) ∈ q₂
      · exact hc
      · simp [VotingConfiguration.hasQuorum, X₀, hc] at h₂
    exact ⟨0, m₁, m₂⟩
  let s₀ : ClusterState Unit :=
    ⟨0, 0, 0, VotingConfiguration.EMPTY_CONFIG, VotingConfiguration.EMPTY_CONFIG, none, false, false, ()⟩
  let W₀ : Cluster Unit := ⟨fun n => CoordinationState.init (P.dn n) 0 s₀, fun _ => False⟩
  have r₀ : Reachable P W₀ := Reachable.init _ ⟨fun n => ⟨s₀, rfl, rfl, rfl, rfl⟩, fun _ h => h⟩
  -- 1. node 0 bootstraps with {0}
  let s₁ : ClusterState Unit := ⟨0, 0, 0, X₀, X₀, none, false, false, ()⟩
  have r₁ := Reachable.step _ _ r₀ (Step.bootstrap (P := P) W₀ 0 X₀ s₁ _ rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ rfl)
  -- 2. node 0 starts an election in term 1 (a join from 0 to 0)
  have r₂ := Reachable.step _ _ r₁ (Step.startJoin (P := P) _ 0 0 1 _ _ rfl rfl)
  -- 3. node 0 handles its own join: it wins term 1
  have r₃ := Reachable.step _ _ r₂ (Step.join (P := P) _ 0 ⟨P.dn 0, P.dn 0, 1, 0, 0⟩ _ _ (Or.inr rfl) rfl rfl)
  -- 4. node 0 publishes version 1 of term 1
  let s₄ : ClusterState Unit := ⟨1, 1, 0, X₀, X₀, none, false, false, ()⟩
  have r₄ := Reachable.step _ _ r₃ (Step.clientValue (P := P) _ 0 s₄ _ _ rfl rfl)
  -- 5. node 0 accepts it
  have r₅ := Reachable.step _ _ r₄ (Step.publish (P := P) _ 0 0 s₄ 0 0 _ _ (Or.inr rfl) rfl)
  -- 6. node 0 handles its own response: a quorum of {0}, the commit is sent
  have r₆ := Reachable.step _ _ r₅ (Step.respond (P := P) _ 0 0 ⟨1, 1⟩ _ (some ⟨P.dn 0, 1, 1⟩) (Or.inr rfl) rfl)
  exact ⟨P, _, hP, rfl, r₆, ⟨P.dn 0, Or.inr rfl⟩⟩
