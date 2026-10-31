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
  obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
  suffices key : ∀ t' v', Descends W 0 v₀ t' v' → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
      s.term = t' → s.version = v' → ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧
        s'.term = t' ∧ pt' < s'.term ∧ Descends W s'.term s'.version t' v' from
    key _ _ hd src s pt pv hs rfl rfl
  intro t' v' hd'
  induction hd' with
  | refl =>
    intro src s pt pv hs ht _
    have := (hinv.pub_wf _ _ _ _ hs).2.1
    omega
  | step t₁ v₁ t₂ v₂ _ hp ih =>
    intro src s pt pv hs ht hv
    obtain ⟨src₁, s₁, hs₁, h1, h2⟩ := hp
    obtain ⟨-, -, e3, e4⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs₁ (ht.trans h1.symm) (hv.trans h2.symm)
    obtain ⟨-, hpos, hle, -, -⟩ := hinv.pub_wf _ _ _ _ hs
    by_cases hlt : pt < s.term
    · exact ⟨src, s, pt, pv, hs, ht, hlt, by rw [ht, hv]; exact .refl _ _⟩
    · obtain ⟨src₂, s₂, pt₂, pv₂, hs₂, h3, h4, -⟩ := hinv.pub_parent _ _ _ _ hs (by omega)
      obtain ⟨src', s', pt', pv', h5, h6, h7, h8⟩ := ih src₂ s₂ pt₂ pv₂ hs₂ (h3.trans e3) (h4.trans e4)
      refine ⟨src', s', pt', pv', h5, by omega, h7, .step _ _ _ _ _ _ h8 ⟨src₁, s₁, hs₁, h1, h2⟩⟩

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
  by_cases hpub : Published W t v
  · obtain ⟨src, s, pt, pv, hs, hst, hsv⟩ := hpub
    obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
    rw [hst, hsv] at hd
    clear hst hsv hs
    induction hd with
    | refl =>
      refine Or.inr (fun et ev hc hd' => ?_)
      have := (inv_committed_published P W hinv et ev hc).1
      rcases inv_descends_key P W hinv _ _ _ _ hd' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    | step t₁ v₁ t₂ v₂ _ hp ih =>
      obtain ⟨src', s', hs', hst', hsv'⟩ := hp
      have hsplit : ∀ ft fv, Descends W ft fv t₂ v₂ → (ft = t₂ ∧ fv = v₂) ∨ Descends W ft fv t₁ v₁ := by
        intro ft fv hf
        by_cases he : ft = t₂ ∧ fv = v₂
        · exact Or.inl he
        · exact Or.inr (inv_descends_parent P W hinv ft fv src' s' t₁ v₁ hs' (by rw [hst', hsv']; exact hf)
            (by rw [hst', hsv']; exact he))
      have hpar : Descends W t₁ v₁ t₂ v₂ := .step _ _ _ _ _ _ (.refl _ _) ⟨src', s', hs', hst', hsv'⟩
      by_cases hc₂ : Committed W t₂ v₂
      · exact Or.inl ⟨t₂, v₂, hc₂, .refl _ _, fun _ _ _ h => h⟩
      · have notself : ∀ et ev, Committed W et ev → ¬ (et = t₂ ∧ ev = v₂) := by
          rintro et ev hc ⟨rfl, rfl⟩; exact hc₂ hc
        rcases ih with ⟨dt, dv, h1, h2, h3⟩ | hnone
        · refine Or.inl ⟨dt, dv, h1, descends_trans W _ _ _ _ _ _ h2 hpar, fun et ev hc hd' => ?_⟩
          rcases hsplit et ev hd' with he | he
          · exact absurd he (notself et ev hc)
          · exact h3 et ev hc he
        · refine Or.inr (fun et ev hc hd' => ?_)
          rcases hsplit et ev hd' with he | he
          · exact notself et ev hc he
          · exact hnone et ev hc he
  · -- an unpublished key has no proper ancestor, and committed keys are published
    refine Or.inr (fun et ev hc hd' => ?_)
    cases hd' with
    | refl => exact hpub (inv_committed_published P W hinv _ _ hc).2
    | step t' v' _ _ _ hp =>
      obtain ⟨src, s, hs, h1, h2⟩ := hp
      exact hpub ⟨src, s, t', v', hs, h1, h2⟩

/-- Every committed key has a first committed ancestor-or-self: one with no committed proper ancestor. -/
theorem OpenSearchSafety.inv_first_committed {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) (hc : Committed W t v) :
    ∃ et ev, Committed W et ev ∧ Descends W et ev t v ∧
      ∀ ft fv, Committed W ft fv → Descends W ft fv et ev → ft = et ∧ fv = ev := by
  obtain ⟨-, src, s, pt, pv, hs, hst, hsv⟩ := inv_committed_published P W hinv t v hc
  obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
  rw [hst, hsv] at hd
  suffices key : ∀ t' v', Descends W 0 v₀ t' v' → ∀ et ev, Committed W et ev → Descends W et ev t' v' →
      ∃ et ev, Committed W et ev ∧ Descends W et ev t' v' ∧
        ∀ ft fv, Committed W ft fv → Descends W ft fv et ev → ft = et ∧ fv = ev from
    key _ _ hd t v hc (.refl _ _)
  intro t' v' hd'
  induction hd' with
  | refl =>
    intro et ev hce hde
    exfalso
    have := (inv_committed_published P W hinv et ev hce).1
    rcases inv_descends_key P W hinv _ _ _ _ hde with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  | step t₁ v₁ t₂ v₂ _ hp ih =>
    intro et ev hce hde
    obtain ⟨src', s', hs', hst', hsv'⟩ := hp
    have hsplit : ∀ ft fv, Descends W ft fv t₂ v₂ → (ft = t₂ ∧ fv = v₂) ∨ Descends W ft fv t₁ v₁ := by
      intro ft fv hf
      by_cases he : ft = t₂ ∧ fv = v₂
      · exact Or.inl he
      · exact Or.inr (inv_descends_parent P W hinv ft fv src' s' t₁ v₁ hs' (by rw [hst', hsv']; exact hf)
          (by rw [hst', hsv']; exact he))
    have hpar : Descends W t₁ v₁ t₂ v₂ := .step _ _ _ _ _ _ (.refl _ _) ⟨src', s', hs', hst', hsv'⟩
    by_cases hex : ∃ ft fv, Committed W ft fv ∧ Descends W ft fv t₁ v₁
    · obtain ⟨ft, fv, hf1, hf2⟩ := hex
      obtain ⟨e₁, e₂, k1, k2, k3⟩ := ih ft fv hf1 hf2
      exact ⟨e₁, e₂, k1, descends_trans W _ _ _ _ _ _ k2 hpar, k3⟩
    · have he : et = t₂ ∧ ev = v₂ := by
        rcases hsplit et ev hde with he | he
        · exact he
        · exact absurd ⟨et, ev, hce, he⟩ hex
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨et, ev, hce, .refl _ _, fun ft fv hf1 hf2 => ?_⟩
      rcases hsplit ft fv hf2 with h' | h'
      · exact h'
      · exact absurd ⟨ft, fv, hf1, h'⟩ hex

/-- Between a key `d` and a committed proper descendant `c` of it, there is a committed key `e` closest to `d`: every
committed key between `d` and `e` is `d` or `e`. -/
theorem OpenSearchSafety.inv_first_committed_after {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (dt ct : Nat) (dv cv : Int) (h : Descends W dt dv ct cv) (hne : ¬ (dt = ct ∧ dv = cv))
    (hc : Committed W ct cv) :
    ∃ et ev, Committed W et ev ∧ Descends W dt dv et ev ∧ ¬ (dt = et ∧ dv = ev) ∧ Descends W et ev ct cv ∧
      ∀ ft fv, Committed W ft fv → Descends W dt dv ft fv → Descends W ft fv et ev →
        (ft = dt ∧ fv = dv) ∨ (ft = et ∧ fv = ev) := by
  -- antisymmetry of descent
  have hanti : ∀ a b c d, Descends W a b c d → Descends W c d a b → a = c ∧ b = d := by
    intro a b c d h₁ h₂
    rcases inv_descends_key P W hinv _ _ _ _ h₁ with h | ⟨-, h₁'⟩
    · exact h
    · rcases inv_descends_key P W hinv _ _ _ _ h₂ with ⟨h, h'⟩ | ⟨-, h₂'⟩
      · exact ⟨h.symm, h'.symm⟩
      · omega
  -- strengthened: from any committed key strictly after `d` on the way to `c'`
  suffices key : ∀ t' v', Descends W dt dv t' v' → ∀ et ev, Committed W et ev → Descends W dt dv et ev →
      ¬ (dt = et ∧ dv = ev) → Descends W et ev t' v' →
      ∃ et ev, Committed W et ev ∧ Descends W dt dv et ev ∧ ¬ (dt = et ∧ dv = ev) ∧ Descends W et ev t' v' ∧
        ∀ ft fv, Committed W ft fv → Descends W dt dv ft fv → Descends W ft fv et ev →
          (ft = dt ∧ fv = dv) ∨ (ft = et ∧ fv = ev) from
    key _ _ h ct cv hc h hne (.refl _ _)
  intro t' v' hd
  induction hd with
  | refl =>
    intro et ev _ h₁ hne' h₂
    exact absurd (hanti _ _ _ _ h₁ h₂) hne'
  | step t₁ v₁ t₂ v₂ hd₁ hp ih =>
    intro et ev hce h₁ hne' h₂
    obtain ⟨src, s, hs, hst, hsv⟩ := hp
    -- an ancestor-or-self of `(t₂, v₂)` is `(t₂, v₂)` or an ancestor-or-self of its parent
    have hsplit : ∀ ft fv, Descends W ft fv t₂ v₂ → (ft = t₂ ∧ fv = v₂) ∨ Descends W ft fv t₁ v₁ := by
      intro ft fv hf
      by_cases he : ft = t₂ ∧ fv = v₂
      · exact Or.inl he
      · exact Or.inr (inv_descends_parent P W hinv ft fv src s t₁ v₁ hs (by rw [hst, hsv]; exact hf)
          (by rw [hst, hsv]; exact he))
    have hpar : Descends W t₁ v₁ t₂ v₂ := .step _ _ _ _ _ _ (.refl _ _) ⟨src, s, hs, hst, hsv⟩
    by_cases hex : ∃ ft fv, Committed W ft fv ∧ Descends W dt dv ft fv ∧ ¬ (dt = ft ∧ dv = fv) ∧
        Descends W ft fv t₁ v₁
    · obtain ⟨ft, fv, hf1, hf2, hf3, hf4⟩ := hex
      obtain ⟨e₁, e₂, k1, k2, k3, k4, k5⟩ := ih ft fv hf1 hf2 hf3 hf4
      exact ⟨e₁, e₂, k1, k2, k3, descends_trans W _ _ _ _ _ _ k4 hpar, k5⟩
    · -- no committed key strictly between `d` and the parent: the committed key is `(t₂, v₂)` itself
      have hc₂ : et = t₂ ∧ ev = v₂ := by
        rcases hsplit et ev h₂ with he | he
        · exact he
        · exact absurd ⟨et, ev, hce, h₁, hne', he⟩ hex
      obtain ⟨rfl, rfl⟩ := hc₂
      refine ⟨et, ev, hce, h₁, hne', .refl _ _, ?_⟩
      intro ft fv hf1 hf2 hf3
      rcases hsplit ft fv hf3 with he | he
      · exact Or.inr he
      · by_cases hfd : dt = ft ∧ dv = fv
        · exact Or.inl ⟨hfd.1.symm, hfd.2.symm⟩
        · exact absurd ⟨ft, fv, hf1, hf2, hfd, he⟩ hex

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
  suffices key : ∀ t' v', Descends W sD.term sD.version t' v' → ¬ (sD.term = t' ∧ sD.version = v') →
      (∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv t' v' →
        (ft = sD.term ∧ fv = sD.version) ∨ (ft = t' ∧ fv = v')) →
      ∀ srcE sE ptE pvE, W.sent (.publishRequest srcE sE ptE pvE) → sE.term = t' → sE.version = v' →
      sE.lastCommittedConfiguration = sD.lastAcceptedConfiguration ∨
      sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration from
    key _ _ h hne hint srcE sE ptE pvE hE rfl rfl
  intro t' v' hd
  induction hd with
  | refl => intro hne; exact absurd ⟨rfl, rfl⟩ hne
  | step t₁ v₁ t₂ v₂ hd₁ hp ih =>
    intro _ hint srcE sE ptE pvE hE ht hv
    obtain ⟨src₁, s₁, hs₁, h1, h2⟩ := hp
    have hpar : Parent W t₁ v₁ t₂ v₂ := ⟨src₁, s₁, hs₁, h1, h2⟩
    obtain ⟨-, -, e3, e4⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hE hs₁ (ht.trans h1.symm) (hv.trans h2.symm)
    have hDpos := (hinv.pub_wf _ _ _ _ hD).2.1
    have hEv := (hinv.pub_wf _ _ _ _ hE).2.2.2.1
    have ht₁ : 1 ≤ t₁ := by
      rcases inv_descends_key P W hinv _ _ _ _ hd₁ with ⟨h5, -⟩ | ⟨h5, -⟩ <;> omega
    obtain ⟨src₂, s₂, pt₂, pv₂, hs₂, h3, h4, hR1, hR2⟩ := hinv.pub_parent _ _ _ _ hE (by omega)
    have h3' : s₂.term = t₁ := h3.trans e3
    have h4' : s₂.version = v₁ := h4.trans e4
    by_cases hD1 : sD.term = t₁ ∧ sD.version = v₁
    · -- the parent of `E` is `D`
      obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hD hs₂ (hD1.1.trans h3'.symm)
        (hD1.2.trans h4'.symm)
      by_cases hac : sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration
      · exact Or.inr hac
      · exact Or.inl (hR2 hac)
    · -- the parent is strictly between `D` and `E`, hence not committed
      have hnc : ¬ Committed W t₁ v₁ := by
        intro hc
        rcases hint t₁ v₁ hc hd₁ (.step _ _ _ _ _ _ (.refl _ _) hpar) with h5 | ⟨-, h5⟩
        · exact hD1 ⟨h5.1.symm, h5.2.symm⟩
        · omega
      have hl : sE.lastCommittedConfiguration = s₂.lastCommittedConfiguration := by
        rcases hR1 with hl | ⟨-, hc⟩
        · exact hl
        · rw [e3, e4] at hc; exact absurd hc hnc
      have ih' := ih hD1 (fun ft fv hfc hf1 hf2 => by
          rcases hint ft fv hfc hf1 (.step _ _ _ _ _ _ hf2 hpar) with h5 | ⟨-, h5⟩
          · exact Or.inl h5
          · exfalso
            rcases inv_descends_key P W hinv _ _ _ _ hf2 with ⟨-, h6⟩ | ⟨-, h6⟩ <;> omega)
        src₂ s₂ pt₂ pv₂ hs₂ h3' h4'
      rcases ih' with h5 | h5
      · exact Or.inl (hl.trans h5)
      · by_cases hac : sE.lastAcceptedConfiguration = s₂.lastAcceptedConfiguration
        · exact Or.inr (hac.trans h5)
        · exact Or.inl ((hR2 hac).trans h5)

/-- A publication without committed proper ancestor has a bootstrap configuration as last committed configuration: the
last committed configuration is copied from the parent unless the parent is committed. -/
theorem OpenSearchSafety.inv_root_lcc {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv))
    (hroot : ∀ ft fv, Committed W ft fv → Descends W ft fv s.term s.version → ft = s.term ∧ fv = s.version) :
    P.initConfs s.lastCommittedConfiguration := by
  obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
  suffices key : ∀ t' v', Descends W 0 v₀ t' v' → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
      s.term = t' → s.version = v' →
      (∀ ft fv, Committed W ft fv → Descends W ft fv t' v' → ft = t' ∧ fv = v') →
      P.initConfs s.lastCommittedConfiguration from
    key _ _ hd src s pt pv hs rfl rfl hroot
  intro t' v' hd'
  induction hd' with
  | refl =>
    intro src s pt pv hs ht _ _
    have := (hinv.pub_wf _ _ _ _ hs).2.1
    omega
  | step t₁ v₁ t₂ v₂ _ hp ih =>
    intro src s pt pv hs ht hv hroot
    obtain ⟨src₁, s₁, hs₁, h1, h2⟩ := hp
    obtain ⟨-, -, e3, e4⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs₁ (ht.trans h1.symm) (hv.trans h2.symm)
    obtain ⟨-, -, -, hpv, hroot0⟩ := hinv.pub_wf _ _ _ _ hs
    by_cases h0 : pt = 0
    · exact hroot0 h0
    · obtain ⟨src₂, s₂, pt₂, pv₂, hs₂, h3, h4, hR1, -⟩ := hinv.pub_parent _ _ _ _ hs (by omega)
      -- the parent is a proper ancestor, hence not committed
      have hpar : Descends W pt pv t₂ v₂ := .step _ _ _ _ _ _ (.refl _ _) ⟨src, s, hs, ht, hv⟩
      have hnc : ¬ Committed W pt pv := by
        intro hc
        obtain ⟨-, hpv'⟩ := hroot pt pv hc hpar
        omega
      rw [hR1.resolve_right (fun h => hnc h.2)]
      apply ih src₂ s₂ pt₂ pv₂ hs₂ (h3.trans e3) (h4.trans e4)
      intro ft fv hfc hfd
      exfalso
      rw [← e3, ← e4] at hfd
      obtain ⟨-, hfv⟩ := hroot ft fv hfc (descends_trans W _ _ _ _ _ _ hfd hpar)
      rcases inv_descends_key P W hinv _ _ _ _ hfd with ⟨-, h5⟩ | ⟨-, h5⟩ <;> omega

/-- (EC) The publish responses to the committed key `c` closest above a publication `D` (no committed key strictly in
between) include a quorum of `D`'s last accepted configuration. -/
theorem OpenSearchSafety.inv_commit_quorum_after {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (srcD : NodeId) (sD : ClusterState V) (ptD : Nat) (pvD : Int) (hD : W.sent (.publishRequest srcD sD ptD pvD))
    (ct : Nat) (cv : Int) (hc : Committed W ct cv) (h : Descends W sD.term sD.version ct cv)
    (hne : ¬ (sD.term = ct ∧ sD.version = cv))
    (hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv ct cv →
      (ft = sD.term ∧ fv = sD.version) ∨ (ft = ct ∧ fv = cv)) :
    ∃ A, RespVoters P W ct cv A ∧ sD.lastAcceptedConfiguration.hasQuorum A = true := by
  obtain ⟨src, hc'⟩ := hc
  obtain ⟨srcC, sC, ptC, pvC, hC, h1, h2, A, hA, h3, h4⟩ := hinv.commit_quorum _ hc'
  have h1' : sC.term = ct := h1
  have h2' : sC.version = cv := h2
  refine ⟨A, hA, ?_⟩
  rcases h4 with h4 | ⟨h4, srcQ, sQ, ptQ, pvQ, hQ, h5, h6, h7⟩
  · -- the path summary from `D` to the committed key
    rcases inv_lineage P W hinv srcD srcC sD sC ptD ptC pvD pvC hD hC (by rw [h1', h2']; exact h)
      (by rw [h1', h2']; exact hne) (by rw [h1', h2']; exact hint) with hl | hl
    · rw [← hl]; exact h4
    · rw [← hl]; exact h3
  · -- (D1) the committed parent of the key lies between `D` and the key, so it is `D`
    have hdp : Descends W sD.term sD.version ptC pvC :=
      inv_descends_parent P W hinv _ _ srcC sC ptC pvC hC (by rw [h1', h2']; exact h) (by rw [h1', h2']; exact hne)
    have hpc : Descends W ptC pvC ct cv := .step _ _ _ _ _ _ (.refl _ _) ⟨srcC, sC, hC, h1', h2'⟩
    rcases hint ptC pvC h4 hdp hpc with ⟨e1, e2⟩ | ⟨-, e2⟩
    · obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hD hQ (e1.symm.trans h5.symm) (e2.symm.trans h6.symm)
      rw [h7]; exact h3
    · exfalso
      have := (hinv.pub_wf _ _ _ _ hC).2.2.2.1
      omega

/-- (EC at a root) The publish responses to a committed key without committed proper ancestor include a quorum of a
bootstrap configuration. -/
theorem OpenSearchSafety.inv_commit_quorum_first {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (ct : Nat) (cv : Int) (hc : Committed W ct cv)
    (hroot : ∀ ft fv, Committed W ft fv → Descends W ft fv ct cv → ft = ct ∧ fv = cv) :
    ∃ X A, P.initConfs X ∧ RespVoters P W ct cv A ∧ X.hasQuorum A = true := by
  obtain ⟨src, h⟩ := hc
  obtain ⟨src', s, pt, pv, hs, h1, h2, A, hA, -, h4⟩ := hinv.commit_quorum _ h
  have h1' : s.term = ct := h1
  have h2' : s.version = cv := h2
  rcases h4 with h4 | ⟨h4, -⟩
  · refine ⟨s.lastCommittedConfiguration, A, ?_, hA, h4⟩
    apply inv_root_lcc P W hinv src' s pt pv hs
    intro ft fv hfc hfd
    rw [h1', h2'] at hfd ⊢
    exact hroot ft fv hfc hfd
  · -- the parent is a committed proper ancestor
    exfalso
    have hd : Descends W pt pv ct cv := .step _ _ _ _ _ _ (.refl _ _) ⟨src', s, hs, h1', h2'⟩
    obtain ⟨-, hpv⟩ := hroot pt pv h4 hd
    have := (hinv.pub_wf _ _ _ _ hs).2.2.2.1
    omega

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
  have hanti : ∀ a b c d, Descends W a b c d → Descends W c d a b → a = c ∧ b = d := by
    intro a b c d h₁ h₂
    rcases inv_descends_key P W hinv _ _ _ _ h₁ with h | ⟨-, h₁'⟩
    · exact h
    · rcases inv_descends_key P W hinv _ _ _ _ h₂ with ⟨h, h'⟩ | ⟨-, h₂'⟩
      · exact ⟨h.symm, h'.symm⟩
      · omega
  rcases inv_deepest_committed P W hinv bt bv with ⟨dt, dv, hdc, hdd, hmax⟩ | hnone
  · left
    obtain ⟨hdpos, srcD, sD, ptD, pvD, hD, hDt, hDv⟩ := inv_committed_published P W hinv dt dv hdc
    subst hDt hDv
    refine ⟨srcD, sD, ptD, pvD, hD, hdc, hdd, hmax, ?_⟩
    by_cases heq : sD.term = bt ∧ sD.version = bv
    · -- the base is the deepest committed key itself
      rcases hr with ⟨h0, -⟩ | ⟨src, s, pt, pv, hs, h1, h2, h3, -⟩
      · omega
      · obtain ⟨-, rfl, -, -⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hD hs (heq.1.trans h1.symm)
          (heq.2.trans h2.symm)
        exact Or.inr h3
    · -- the base is strictly below it: uncommitted, so realized by its own configurations
      rcases hr with ⟨h0, -⟩ | ⟨src, s, pt, pv, hs, h1, h2, h3, h4⟩
      · rcases inv_descends_key P W hinv _ _ _ _ hdd with ⟨h5, -⟩ | ⟨h5, -⟩ <;> omega
      · have hbnc : ¬ Committed W bt bv := fun hc => heq (hanti _ _ _ _ hdd (hmax bt bv hc (.refl _ _)))
        have hx : x = s.lastCommittedConfiguration := h4.resolve_right (fun h => hbnc h.2)
        have hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv →
            Descends W ft fv s.term s.version →
            (ft = sD.term ∧ fv = sD.version) ∨ (ft = s.term ∧ fv = s.version) := by
          intro ft fv hfc hf1 hf2
          rw [h1, h2] at hf2
          have := hanti _ _ _ _ hf1 (hmax ft fv hfc hf2)
          exact Or.inl ⟨this.1.symm, this.2.symm⟩
        rcases inv_lineage P W hinv srcD src sD s ptD pt pvD pv hD hs (by rw [h1, h2]; exact hdd)
          (by rw [h1, h2]; exact heq) hint with hl | hl
        · exact Or.inl (hx.trans hl)
        · exact Or.inr (h3.trans hl)
  · right
    refine ⟨hnone, ?_⟩
    rcases hr with ⟨-, -, hX⟩ | ⟨src, s, pt, pv, hs, h1, h2, -, h4⟩
    · exact hX
    · have hbnc : ¬ Committed W bt bv := fun hc => hnone bt bv hc (.refl _ _)
      rw [h4.resolve_right (fun h => hbnc h.2)]
      apply inv_root_lcc P W hinv src s pt pv hs
      intro ft fv hfc hfd
      rw [h1, h2] at hfd
      exact absurd hfd (hnone ft fv hfc)

/-- (S5 for publications) Every publication's last committed configuration is a bootstrap configuration or the last
accepted configuration of a committed publication. -/
theorem OpenSearchSafety.inv_pub_lcc {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) :
    P.initConfs s.lastCommittedConfiguration ∨
    ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ Committed W s'.term s'.version ∧
      s'.lastAcceptedConfiguration = s.lastCommittedConfiguration := by
  obtain ⟨v₀, hd⟩ := hinv.pub_rooted src s pt pv hs
  suffices key : ∀ t' v', Descends W 0 v₀ t' v' → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) →
      s.term = t' → s.version = v' → P.initConfs s.lastCommittedConfiguration ∨
      ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ Committed W s'.term s'.version ∧
        s'.lastAcceptedConfiguration = s.lastCommittedConfiguration from
    key _ _ hd src s pt pv hs rfl rfl
  intro t' v' hd'
  induction hd' with
  | refl =>
    intro src s pt pv hs ht _
    have := (hinv.pub_wf _ _ _ _ hs).2.1
    omega
  | step t₁ v₁ t₂ v₂ _ hp ih =>
    intro src s pt pv hs ht hv
    obtain ⟨src₁, s₁, hs₁, h1, h2⟩ := hp
    obtain ⟨-, -, e3, e4⟩ := hinv.pub_unique _ _ _ _ _ _ _ _ hs hs₁ (ht.trans h1.symm) (hv.trans h2.symm)
    obtain ⟨-, -, -, -, hroot0⟩ := hinv.pub_wf _ _ _ _ hs
    by_cases h0 : pt = 0
    · exact Or.inl (hroot0 h0)
    · obtain ⟨src₂, s₂, pt₂, pv₂, hs₂, h3, h4, hR1, -⟩ := hinv.pub_parent _ _ _ _ hs (by omega)
      rcases hR1 with hl | ⟨hl, hc⟩
      · rw [hl]; exact ih src₂ s₂ pt₂ pv₂ hs₂ (h3.trans e3) (h4.trans e4)
      · exact Or.inr ⟨src₂, s₂, pt₂, pv₂, hs₂, by rw [h3, h4]; exact hc, hl.symm⟩

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
  have hanti : ∀ a b c d, Descends W a b c d → Descends W c d a b → a = c ∧ b = d := by
    intro a b c d e₁ e₂
    rcases inv_descends_key P W hinv _ _ _ _ e₁ with h | ⟨-, e₁'⟩
    · exact h
    · rcases inv_descends_key P W hinv _ _ _ _ e₂ with ⟨h, h'⟩ | ⟨-, e₂'⟩
      · exact ⟨h.symm, h'.symm⟩
      · omega
  have hle : ∀ a b c d, Descends W a b c d → a ≤ c := by
    intro a b c d e
    rcases inv_descends_key P W hinv _ _ _ _ e with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  induction t using Nat.strongRecOn generalizing L bt bv x y J ct cv with
  | ind t IH =>
  obtain ⟨hbt, hr, hJ, hqx, hqy⟩ := id hrec
  -- leader completeness below `t`
  have LC : ∀ ct cv, Committed W ct cv → ∀ src s pt pv, W.sent (.publishRequest src s pt pv) → ct < s.term →
      s.term < t → Descends W ct cv s.term s.version := by
    intro ct cv hc src s pt pv hs h1 h2
    obtain ⟨L', F, pt', pv', hF, hFt, hFpt, hFd⟩ := inv_reign_first P W hinv src s pt pv hs
    obtain ⟨y', J', hrec'⟩ := hinv.pub_election L' F pt' pv' hF hFpt
    have := IH F.term (by omega) L' pt' pv' F.lastCommittedConfiguration y' J' hrec' ct cv hc (by omega)
    exact descends_trans W _ _ _ _ _ _ (.step _ _ _ _ _ _ this ⟨L', F, hF, rfl, rfl⟩) hFd
  -- committed keys below `t` are comparable
  have S3 : ∀ t₁ v₁ t₂ v₂, Committed W t₁ v₁ → Committed W t₂ v₂ → t₁ < t → t₂ < t →
      Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
    intro t₁ v₁ t₂ v₂ h₁ h₂ ht₁ ht₂
    obtain ⟨-, src₁, s₁, pt₁, pv₁, hs₁, e1, f1⟩ := inv_committed_published P W hinv _ _ h₁
    obtain ⟨-, src₂, s₂, pt₂, pv₂, hs₂, e2, f2⟩ := inv_committed_published P W hinv _ _ h₂
    rcases Nat.lt_trichotomy t₁ t₂ with h | h | h
    · left; have := LC _ _ h₁ _ _ _ _ hs₂ (by omega) (by omega); rwa [e2, f2] at this
    · rcases hinv.pub_same_term _ _ _ _ _ _ _ _ hs₁ hs₂ (by omega) with h' | h'
      · left; rwa [e1, f1, e2, f2] at h'
      · right; rwa [e1, f1, e2, f2] at h'
    · right; have := LC _ _ h₂ _ _ _ _ hs₁ (by omega) (by omega); rwa [e1, f1] at this
  -- a committed key of an older term accepted by a voter of `J` is an ancestor of the base
  have finish : ∀ c't c'v, Committed W c't c'v → c't < t →
      (∃ m, m ∈ J ∧ ∃ d, W.sent (.publishResponse m d ⟨c't, c'v⟩)) → Descends W c't c'v bt bv := by
    intro c't c'v hc' hlt' ⟨m, hmJ, d, hmr⟩
    obtain ⟨hme, j, hj, hjs, -, hjt, hjb⟩ := hJ m hmJ
    have hk := hinv.join_after_response j m d ⟨c't, c'v⟩ hj hmr hjs hme (by dsimp only; omega)
    obtain ⟨hc'pos, srcC, sC, ptC, pvC, hsC, eC, fC⟩ := inv_committed_published P W hinv _ _ hc'
    unfold KeyLE at hk
    unfold Below at hjb
    dsimp only at hk
    rcases hr with ⟨h0, -⟩ | ⟨srcB, sB, ptB, pvB, hsB, hBt, hBv, -⟩
    · exfalso; omega
    · rcases Nat.lt_or_ge c't bt with h5 | h5
      · have := LC _ _ hc' _ _ _ _ hsB (by omega) (by omega)
        rwa [hBt, hBv] at this
      · have h7 : c'v ≤ bv := by omega
        rcases hinv.pub_same_term _ _ _ _ _ _ _ _ hsC hsB (by omega) with h' | h'
        · rwa [eC, fC, hBt, hBv] at h'
        · rw [eC, fC, hBt, hBv] at h'
          rcases inv_descends_key P W hinv _ _ _ _ h' with ⟨h8, h9⟩ | ⟨-, h9⟩
          · rw [← h8, ← h9]; exact .refl _ _
          · omega
  rcases inv_pivot P W hinv bt bv x y hr with ⟨srcD, sD, ptD, pvD, hD, hcD, hdD, hmax, hk⟩ | ⟨hnone, hX⟩
  · -- (I) the base has a deepest committed ancestor `D`
    have hDt : sD.term < t := by have := hle _ _ _ _ hdD; omega
    rcases S3 _ _ _ _ hcD hc hDt hlt with hDC | hCD
    · by_cases heq : sD.term = ct ∧ sD.version = cv
      · rw [← heq.1, ← heq.2]; exact hdD
      · -- the first committed key `C'` after `D` on the way to the committed key
        obtain ⟨c't, c'v, hc', hdc', hne', hc'c, hint⟩ := inv_first_committed_after P W hinv _ _ _ _ hDC heq hc
        obtain ⟨A, hA, hqA⟩ := inv_commit_quorum_after P W hinv srcD sD ptD pvD hD c't c'v hc' hdc' hne' hint
        have hqJ : sD.lastAcceptedConfiguration.hasQuorum J = true := by
          rcases hk with h | h <;> rw [← h] <;> assumption
        obtain ⟨m, -, hmA, hmJ⟩ := quorum_intersect _ _ _ hqA hqJ
        have hb := finish c't c'v hc' (by have := hle _ _ _ _ hc'c; omega) ⟨m, hmJ, (hA m hmA).2⟩
        -- but `C'` lies strictly below the deepest committed ancestor `D`: contradiction
        exact absurd (hanti _ _ _ _ hdc' (hmax _ _ hc' hb)) hne'
    · exact descends_trans W _ _ _ _ _ _ hCD hdD
  · -- (II) the base has no committed ancestor: the first committed key of the committed key's branch
    obtain ⟨c't, c'v, hc', hc'c, hmin⟩ := inv_first_committed P W hinv ct cv hc
    obtain ⟨X', A, hX', hA, hqA⟩ := inv_commit_quorum_first P W hinv c't c'v hc' hmin
    obtain ⟨m, hmJ, hmA⟩ := hP x X' hX hX' J A (fun z hz => (hJ z hz).1) (fun z hz => (hA z hz).1) hqx hqA
    exact absurd (finish c't c'v hc' (by have := hle _ _ _ _ hc'c; omega) ⟨m, hmJ, (hA m hmA).2⟩)
      (hnone c't c'v hc')

/-- (Leader completeness) Every publication of a later term descends from every committed key. -/
theorem OpenSearchSafety.inv_leader_completeness {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (v : Int) (hc : Committed W t v) (src : NodeId) (s : ClusterState V) (pt : Nat)
    (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) (hlt : t < s.term) :
    Descends W t v s.term s.version := by
  obtain ⟨L, F, pt', pv', hF, hFt, hFpt, hFd⟩ := inv_reign_first P W hinv src s pt pv hs
  obtain ⟨y, J, hrec⟩ := hinv.pub_election L F pt' pv' hF hFpt
  have h1 := inv_elc P hP W hinv L F.term pt' pv' F.lastCommittedConfiguration y J hrec t v hc
    (by rw [hFt]; exact hlt)
  exact descends_trans W _ _ _ _ _ _ (.step _ _ _ _ _ _ h1 ⟨L, F, hF, rfl, rfl⟩) hFd

/-- (S3) Committed keys are totally ordered by descent. -/
theorem OpenSearchSafety.inv_committed_comparable {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t₁ t₂ : Nat) (v₁ v₂ : Int) (h₁ : Committed W t₁ v₁) (h₂ : Committed W t₂ v₂) :
    Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by
  obtain ⟨-, src₁, s₁, pt₁, pv₁, hs₁, ht₁, hv₁⟩ := inv_committed_published P W hinv t₁ v₁ h₁
  obtain ⟨-, src₂, s₂, pt₂, pv₂, hs₂, ht₂, hv₂⟩ := inv_committed_published P W hinv t₂ v₂ h₂
  rcases Nat.lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · left
    have := inv_leader_completeness P hP W hinv t₁ v₁ h₁ src₂ s₂ pt₂ pv₂ hs₂ (by rw [ht₂]; exact hlt)
    rw [ht₂, hv₂] at this
    exact this
  · rcases hinv.pub_same_term _ _ _ _ _ _ _ _ hs₁ hs₂ (ht₁.trans (heq.trans ht₂.symm)) with h | h
    · left; rw [ht₁, hv₁, ht₂, hv₂] at h; exact h
    · right; rw [ht₁, hv₁, ht₂, hv₂] at h; exact h
  · right
    have := inv_leader_completeness P hP W hinv t₂ v₂ h₂ src₁ s₁ pt₁ pv₁ hs₁ (by rw [ht₁]; exact hgt)
    rw [ht₁, hv₁] at this
    exact this

/-- (ESL) Two election records of the same term share a voter: their bases have the same pivot (by `inv_elc`), whose
last accepted configuration both voter lists are quorums of, or both bases have no committed ancestor and the voter
lists are quorums of two bootstrap configurations (`P.InitCompatible`). -/
theorem OpenSearchSafety.inv_election_quorums {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (L₁ L₂ : NodeId) (bt₁ bt₂ : Nat) (bv₁ bv₂ : Int)
    (x₁ y₁ x₂ y₂ : VotingConfiguration) (J₁ J₂ : List NodeId)
    (h₁ : ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁) (h₂ : ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂) :
    ∃ m, m ∈ J₁ ∧ m ∈ J₂ := by
  have hanti : ∀ a b c d, Descends W a b c d → Descends W c d a b → a = c ∧ b = d := by
    intro a b c d e₁ e₂
    rcases inv_descends_key P W hinv _ _ _ _ e₁ with h | ⟨-, e₁'⟩
    · exact h
    · rcases inv_descends_key P W hinv _ _ _ _ e₂ with ⟨h, h'⟩ | ⟨-, e₂'⟩
      · exact ⟨h.symm, h'.symm⟩
      · omega
  obtain ⟨hlt₁, hr₁, hJ₁, hq₁x, hq₁y⟩ := id h₁
  obtain ⟨hlt₂, hr₂, hJ₂, hq₂x, hq₂y⟩ := id h₂
  -- a committed ancestor of a base of term < t has term < t
  have hlow : ∀ dt dv bt bv, Descends W dt dv bt bv → bt < t → dt < t := by
    intro dt dv bt bv hd hb
    rcases inv_descends_key P W hinv _ _ _ _ hd with ⟨h5, -⟩ | ⟨h5, -⟩ <;> omega
  rcases inv_pivot P W hinv bt₁ bv₁ x₁ y₁ hr₁ with ⟨srcD₁, sD₁, ptD₁, pvD₁, hD₁, hc₁, hd₁, hmax₁, hk₁⟩ |
      ⟨hnone₁, hX₁⟩ <;>
    rcases inv_pivot P W hinv bt₂ bv₂ x₂ y₂ hr₂ with ⟨srcD₂, sD₂, ptD₂, pvD₂, hD₂, hc₂, hd₂, hmax₂, hk₂⟩ |
      ⟨hnone₂, hX₂⟩
  · -- both bases have committed pivots: by election leader completeness, it is the same pivot
    have e12 := hmax₁ _ _ hc₂ (inv_elc P hP W hinv L₁ t bt₁ bv₁ x₁ y₁ J₁ h₁ _ _ hc₂ (hlow _ _ _ _ hd₂ hlt₂))
    have e21 := hmax₂ _ _ hc₁ (inv_elc P hP W hinv L₂ t bt₂ bv₂ x₂ y₂ J₂ h₂ _ _ hc₁ (hlow _ _ _ _ hd₁ hlt₁))
    obtain ⟨et, ev⟩ := hanti _ _ _ _ e12 e21
    have hs12 : sD₁ = sD₂ := (hinv.pub_unique _ _ _ _ _ _ _ _ hD₁ hD₂ et.symm ev.symm).2.1
    have q₁ : sD₁.lastAcceptedConfiguration.hasQuorum J₁ = true := by
      rcases hk₁ with h | h <;> rw [← h] <;> assumption
    have q₂ : sD₂.lastAcceptedConfiguration.hasQuorum J₂ = true := by
      rcases hk₂ with h | h <;> rw [← h] <;> assumption
    rw [hs12] at q₁
    obtain ⟨m, -, hm₁, hm₂⟩ := quorum_intersect _ _ _ q₁ q₂
    exact ⟨m, hm₁, hm₂⟩
  · exfalso
    exact hnone₂ _ _ hc₁ (inv_elc P hP W hinv L₂ t bt₂ bv₂ x₂ y₂ J₂ h₂ _ _ hc₁ (hlow _ _ _ _ hd₁ hlt₁))
  · exfalso
    exact hnone₁ _ _ hc₂ (inv_elc P hP W hinv L₁ t bt₁ bv₁ x₁ y₁ J₁ h₁ _ _ hc₂ (hlow _ _ _ _ hd₂ hlt₂))
  · -- neither base has a committed ancestor: two quorums of bootstrap configurations
    exact hP x₁ x₂ hX₁ hX₂ J₁ J₂ (fun x hx => (hJ₁ x hx).1) (fun x hx => (hJ₂ x hx).1) hq₁x hq₂x

/-- Two election records of the same term are of the same candidate (their common voter sent one join per term). -/
theorem OpenSearchSafety.inv_election_unique {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (L₁ L₂ : NodeId) (bt₁ bt₂ : Nat) (bv₁ bv₂ : Int)
    (x₁ y₁ x₂ y₂ : VotingConfiguration) (J₁ J₂ : List NodeId)
    (h₁ : ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁) (h₂ : ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂) :
    L₁ = L₂ := by
  obtain ⟨m, hm₁, hm₂⟩ := inv_election_quorums P hP W hinv t L₁ L₂ bt₁ bt₂ bv₁ bv₂ x₁ y₁ x₂ y₂ J₁ J₂ h₁ h₂
  obtain ⟨-, -, hJ₁, -, -⟩ := h₁
  obtain ⟨-, -, hJ₂, -, -⟩ := h₂
  obtain ⟨he, j₁, hj₁, hs₁, ht₁, hterm₁, -⟩ := hJ₁ m hm₁
  obtain ⟨-, j₂, hj₂, hs₂, ht₂, hterm₂, -⟩ := hJ₂ m hm₂
  have hjj := hinv.join_unique j₁ j₂ hj₁ hj₂ (by rw [hs₁]; exact he) (hs₁.trans hs₂.symm)
    (hterm₁.trans hterm₂.symm)
  rw [← ht₁, ← ht₂, hjj]
