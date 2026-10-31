import Definitions.Def_OpenSearchSafety

open OpenSearchCoordination OpenSearchSafety

/-! # OpenSearch cluster coordination: consequences of the invariant inside one cluster

Everything here is about a single cluster `W` satisfying `Inv P W`; nothing here mentions steps. The publications form
a forest (`Descends`, rooted at term-0 keys); the facts below are, in dependency order:
* descent: transitivity, keys grow along descent, the last step of a descent goes through the parent, the ancestors of
  a key are totally ordered, the first publication of a term (`inv_reign_first`);
* committed keys along a branch: the deepest committed ancestor (`inv_deepest_committed`), the first committed key of a
  branch (`inv_first_committed`) or after a key (`inv_first_committed_after`);
* configurations along a branch: the path summary (`inv_lineage`), the root configuration (`inv_root_lcc`), commit
  quorums seen from below (`inv_commit_quorum_after`, `inv_commit_quorum_first`), the pivot of a realized base
  (`inv_pivot`);
* elections: the base of every election record descends from every older committed key (`inv_elc`), hence leader
  completeness, committed keys are totally ordered, and two election records of one term share a voter and a candidate
  (`inv_election_quorums`, `inv_election_unique`). -/

/-! ## Quorums (as in the per-node mission) -/

/-- Counting: an element satisfying both `p` and `q` is counted at most twice on the left and once on each side. -/
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

/-- No configuration has a quorum of the empty list. -/
private theorem hasQuorum_nil (c : VotingConfiguration) : c.hasQuorum [] = false := by
  unfold VotingConfiguration.hasQuorum
  rw [decide_eq_false_iff_not]
  have : (c.nodeIds.filter (fun x => ([] : List NodeId).contains x)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; simp
  omega

/-! ## Descent -/

/-- Descent is transitive. -/
theorem OpenSearchSafety.descends_trans {V : Type} (W : Cluster V) (t₁ t₂ t₃ : Nat) (v₁ v₂ v₃ : Int)
    (h₁ : Descends W t₁ v₁ t₂ v₂) (h₂ : Descends W t₂ v₂ t₃ v₃) : Descends W t₁ v₁ t₃ v₃ := by
  induction h₂ with
  | refl => exact h₁
  | step _ _ _ _ _ hp ih => exact .step _ _ _ _ _ _ ih hp

/-- Along a descent the term does not decrease and the version strictly increases, unless the descent is trivial. -/
theorem OpenSearchSafety.inv_descends_key {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t t' : Nat) (v v' : Int) (h : Descends W t v t' v') :
    (t = t' ∧ v = v') ∨ (t ≤ t' ∧ v < v') := by
  induction h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | step _ _ _ _ _ hp ih =>
    obtain ⟨src, s, hs, rfl, rfl⟩ := hp
    obtain ⟨-, -, h1, h2, -⟩ := hinv.pub_wf _ _ _ _ hs
    right
    rcases ih with ⟨rfl, rfl⟩ | ⟨h3, h4⟩ <;> omega

/-- A non-trivial descent into a publication goes through the publication's own parent. -/
theorem OpenSearchSafety.inv_descends_parent {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int)
    (hs : W.sent (.publishRequest src s pt pv)) (h : Descends W t v s.term s.version)
    (hne : ¬ (t = s.term ∧ v = s.version)) : Descends W t v pt pv := by
  cases h with
  | refl => exact absurd ⟨rfl, rfl⟩ hne
  | step t' v' _ _ h' hp =>
    obtain ⟨src₁, s₁, hs₁, h1, h2⟩ := hp
    obtain ⟨-, -, rfl, rfl⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs₁ h1.symm h2.symm
    exact h'

/-- The ancestors of a key are totally ordered by descent (a publication has a single parent). -/
theorem OpenSearchSafety.inv_descends_linear {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t₁ t₂ t : Nat) (v₁ v₂ v : Int) (h₁ : Descends W t₁ v₁ t v) (h₂ : Descends W t₂ v₂ t v) :
    Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
  induction h₂ generalizing t₁ v₁ with
  | refl => exact Or.inl h₁
  | step t' v' t'' v'' h₂' hp ih =>
    cases h₁ with
    | refl => exact Or.inr (.step _ _ _ _ _ _ h₂' hp)
    | step t₀ v₀ _ _ h₁' hp₁ =>
      obtain ⟨src, s, hs, h1, h2⟩ := hp
      obtain ⟨src₁, s₁, hs₁, h3, h4⟩ := hp₁
      obtain ⟨-, -, rfl, rfl⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs₁ (h1.trans h3.symm) (h2.trans h4.symm)
      exact ih _ _ h₁'

/-- Every publication descends from a first publication of its term: one whose parent is of an older term. -/
theorem OpenSearchSafety.inv_reign_first {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) :
    ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ s'.term = s.term ∧ pt' < s'.term ∧
      Descends W s'.term s'.version s.term s.version := by
  sorry

/-! ## Basic facts -/

/-- Every committed key is the key of a publication, of term ≥ 1. -/
theorem OpenSearchSafety.inv_committed_published {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) (h : Committed W t v) :
    1 ≤ t ∧ ∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ s.term = t ∧ s.version = v := by
  obtain ⟨src, h⟩ := h
  obtain ⟨src', s, pt, pv, hs, h1, h2, -⟩ := hinv.commit_quorum _ h
  obtain ⟨-, hpos, -⟩ := hinv.pub_wf _ _ _ _ hs
  have h1' : s.term = t := h1
  exact ⟨by omega, src', s, pt, pv, hs, h1', h2⟩

/-- Only cluster-manager-eligible nodes win elections. -/
theorem OpenSearchSafety.inv_eligible_of_won {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W) (n : NodeId)
    (h : (W.node n).electionWon = true) : P.eligible n = true := by
  obtain ⟨hq, -⟩ := hinv.won_quorum n h
  cases hjv : (W.node n).joinVotes.nodes with
  | nil =>
    unfold VoteCollection.isQuorum at hq
    rw [hjv, hasQuorum_nil] at hq
    cases hq
  | cons m ms =>
    obtain ⟨-, j, hj, -, htgt, -⟩ := hinv.joinVotes_sent n m (by rw [hjv]; exact List.mem_cons_self ..)
    have := (hinv.join_wf j hj).2
    rw [htgt] at this
    exact this

/-- A node that has won the election of its current term has won that term. -/
theorem OpenSearchSafety.inv_won_of_electionWon {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (h : (W.node n).electionWon = true) : Won P W n (W.node n).currentTerm := by
  exact ⟨inv_eligible_of_won P W hinv n h, Or.inl ⟨h, rfl⟩⟩

/-! ## Committed keys along a branch -/

/-- Every key has a deepest committed ancestor-or-self (every committed ancestor-or-self of the key is an ancestor-or-self
of it), or no committed ancestor-or-self at all. -/
theorem OpenSearchSafety.inv_deepest_committed {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) :
    (∃ dt dv, Committed W dt dv ∧ Descends W dt dv t v ∧
      ∀ et ev, Committed W et ev → Descends W et ev t v → Descends W et ev dt dv) ∨
    (∀ et ev, Committed W et ev → ¬ Descends W et ev t v) := by
  sorry

/-- Every committed key has a first committed ancestor-or-self: one with no committed proper ancestor. -/
theorem OpenSearchSafety.inv_first_committed {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) (hc : Committed W t v) :
    ∃ et ev, Committed W et ev ∧ Descends W et ev t v ∧
      ∀ ft fv, Committed W ft fv → Descends W ft fv et ev → ft = et ∧ fv = ev := by
  sorry

/-- Between a key `d` and a committed proper descendant `c` of it, there is a committed key `e` closest to `d`: every
committed key between `d` and `e` is `d` or `e`. -/
theorem OpenSearchSafety.inv_first_committed_after {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (dt ct : Nat) (dv cv : Int) (h : Descends W dt dv ct cv) (hne : ¬ (dt = ct ∧ dv = cv))
    (hc : Committed W ct cv) :
    ∃ et ev, Committed W et ev ∧ Descends W dt dv et ev ∧ ¬ (dt = et ∧ dv = ev) ∧ Descends W et ev ct cv ∧
      ∀ ft fv, Committed W ft fv → Descends W dt dv ft fv → Descends W ft fv et ev →
        (ft = dt ∧ fv = dv) ∨ (ft = et ∧ fv = ev) := by
  sorry

/-! ## Configurations along a branch -/

/-- (Path summary; design 2's lineage lemma) Along a non-trivial descent from a publication `D` to a publication `E` with
no committed key strictly in between, `D`'s last accepted configuration is one of `E`'s two configurations: the last
committed configuration changes only below a committed key, and the last accepted one only when the last committed one
is the parent's last accepted one. -/
theorem OpenSearchSafety.inv_lineage {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (srcD srcE : NodeId) (sD sE : ClusterState V) (ptD ptE : Nat) (pvD pvE : Int)
    (hD : W.sent (.publishRequest srcD sD ptD pvD)) (hE : W.sent (.publishRequest srcE sE ptE pvE))
    (h : Descends W sD.term sD.version sE.term sE.version)
    (hne : ¬ (sD.term = sE.term ∧ sD.version = sE.version))
    (hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv sE.term sE.version →
      (ft = sD.term ∧ fv = sD.version) ∨ (ft = sE.term ∧ fv = sE.version)) :
    sE.lastCommittedConfiguration = sD.lastAcceptedConfiguration ∨
    sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration := by
  sorry

/-- A publication without committed proper ancestor has a bootstrap configuration as last committed configuration: the
last committed configuration is copied from the parent unless the parent is committed. -/
theorem OpenSearchSafety.inv_root_lcc {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv))
    (hroot : ∀ ft fv, Committed W ft fv → Descends W ft fv s.term s.version → ft = s.term ∧ fv = s.version) :
    P.initConfs s.lastCommittedConfiguration := by
  sorry

/-- (EC) The publish responses to the committed key `c` closest above a publication `D` (no committed key strictly in
between) include a quorum of `D`'s last accepted configuration. -/
theorem OpenSearchSafety.inv_commit_quorum_after {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (srcD : NodeId) (sD : ClusterState V) (ptD : Nat) (pvD : Int) (hD : W.sent (.publishRequest srcD sD ptD pvD))
    (ct : Nat) (cv : Int) (hc : Committed W ct cv) (h : Descends W sD.term sD.version ct cv)
    (hne : ¬ (sD.term = ct ∧ sD.version = cv))
    (hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv ct cv →
      (ft = sD.term ∧ fv = sD.version) ∨ (ft = ct ∧ fv = cv)) :
    ∃ A, RespVoters P W ct cv A ∧ sD.lastAcceptedConfiguration.hasQuorum A = true := by
  sorry

/-- (EC at a root) The publish responses to a committed key without committed proper ancestor include a quorum of a
bootstrap configuration. -/
theorem OpenSearchSafety.inv_commit_quorum_first {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (ct : Nat) (cv : Int) (hc : Committed W ct cv)
    (hroot : ∀ ft fv, Committed W ft fv → Descends W ft fv ct cv → ft = ct ∧ fv = cv) :
    ∃ X A, P.initConfs X ∧ RespVoters P W ct cv A ∧ X.hasQuorum A = true := by
  sorry

/-- (Pivot and path summary) If `(x, y)` realizes the key `b`, then either `b` has a deepest committed ancestor-or-self,
a publication whose last accepted configuration is `x` or `y`; or `b` has no committed ancestor-or-self, and `x` is a
bootstrap configuration. -/
theorem OpenSearchSafety.inv_pivot {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (bt : Nat) (bv : Int) (x y : VotingConfiguration) (hr : Realizes P W bt bv x y) :
    (∃ src s pt pv, W.sent (.publishRequest src s pt pv) ∧ Committed W s.term s.version ∧
      Descends W s.term s.version bt bv ∧
      (∀ et ev, Committed W et ev → Descends W et ev bt bv → Descends W et ev s.term s.version) ∧
      (x = s.lastAcceptedConfiguration ∨ y = s.lastAcceptedConfiguration)) ∨
    ((∀ et ev, Committed W et ev → ¬ Descends W et ev bt bv) ∧ P.initConfs x) := by
  sorry

/-- (S5 for publications) Every publication's last committed configuration is a bootstrap configuration or the last
accepted configuration of a committed publication. -/
theorem OpenSearchSafety.inv_pub_lcc {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) :
    P.initConfs s.lastCommittedConfiguration ∨
    ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ Committed W s'.term s'.version ∧
      s'.lastAcceptedConfiguration = s.lastCommittedConfiguration := by
  sorry

/-! ## Elections -/

/-- (Election leader completeness: design 2's L6, the core of design 1's Theorem LC) The base of every election record
for term `t` descends from every committed key of an older term. Proof: strong induction on `t`; the pivot of the base
and the first committed key above it (or above a root) have quorums of a common configuration (or of two compatible
bootstrap configurations), so some voter accepted that key before voting in `t` (`join_after_response`), which bounds
the base from below; the induction hypothesis or `pub_same_term` then makes the key an ancestor of the base. -/
theorem OpenSearchSafety.inv_elc {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V) (hinv : Inv P W)
    (L : NodeId) (t bt : Nat) (bv : Int) (x y : VotingConfiguration) (J : List NodeId)
    (hrec : ElectionRecord P W L t bt bv x y J) (ct : Nat) (cv : Int) (hc : Committed W ct cv) (hlt : ct < t) :
    Descends W ct cv bt bv := by
  sorry

/-- (Leader completeness) Every publication of a later term descends from every committed key. -/
theorem OpenSearchSafety.inv_leader_completeness {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (v : Int) (hc : Committed W t v) (src : NodeId) (s : ClusterState V) (pt : Nat)
    (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) (hlt : t < s.term) :
    Descends W t v s.term s.version := by
  sorry

/-- (S3) Committed keys are totally ordered by descent. -/
theorem OpenSearchSafety.inv_committed_comparable {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t₁ t₂ : Nat) (v₁ v₂ : Int) (h₁ : Committed W t₁ v₁) (h₂ : Committed W t₂ v₂) :
    Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
  sorry

/-- (ESL) Two election records of the same term share a voter: their bases have the same pivot (by `inv_elc`), whose
last accepted configuration both voter lists are quorums of, or both bases have no committed ancestor and the voter
lists are quorums of two bootstrap configurations (`P.InitCompatible`). -/
theorem OpenSearchSafety.inv_election_quorums {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (L₁ L₂ : NodeId) (bt₁ bt₂ : Nat) (bv₁ bv₂ : Int)
    (x₁ y₁ x₂ y₂ : VotingConfiguration) (J₁ J₂ : List NodeId)
    (h₁ : ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁) (h₂ : ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂) :
    ∃ m, m ∈ J₁ ∧ m ∈ J₂ := by
  sorry

/-- Two election records of the same term are of the same candidate (their common voter sent one join per term). -/
theorem OpenSearchSafety.inv_election_unique {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (L₁ L₂ : NodeId) (bt₁ bt₂ : Nat) (bv₁ bv₂ : Int)
    (x₁ y₁ x₂ y₂ : VotingConfiguration) (J₁ J₂ : List NodeId)
    (h₁ : ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁) (h₂ : ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂) :
    L₁ = L₂ := by
  sorry
