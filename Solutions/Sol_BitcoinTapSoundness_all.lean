import Definitions.Def_BitcoinTapSoundness
import Theorems.Thm_BitcoinSer_sha256_length

open BitcoinTapSoundness BitcoinSer BitcoinTaproot

/-! ### Tagged hashes -/

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

/-- Equal tagged hashes have equal tags' hashes and equal messages, or exhibit a SHA-256 collision. -/
theorem BitcoinTapSoundness.tagged_collision (t t' : String) (m m' : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tagged t m = BitcoinTaproot.tagged t' m') :
    (BitcoinSer.sha256 (BitcoinSig.ascii t) = BitcoinSer.sha256 (BitcoinSig.ascii t') ∧ m = m') ∨
      BitcoinTapSoundness.Sha256Collision := by
  simp only [tagged, BitcoinSig.taggedHash] at h
  by_cases heq : sha256 (BitcoinSig.ascii t) ++ sha256 (BitcoinSig.ascii t) ++ m =
      sha256 (BitcoinSig.ascii t') ++ sha256 (BitcoinSig.ascii t') ++ m'
  · left
    have hl : (sha256 (BitcoinSig.ascii t) ++ sha256 (BitcoinSig.ascii t)).length =
        (sha256 (BitcoinSig.ascii t') ++ sha256 (BitcoinSig.ascii t')).length := by
      simp only [List.length_append, BitcoinSer.sha256_length]
    obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ hl heq
    obtain ⟨h3, -⟩ := append_inj_len _ _ _ _ (by simp only [BitcoinSer.sha256_length]) h1
    exact ⟨h3, h2⟩
  · right; exact ⟨_, _, heq, h⟩

/-- The `TapLeaf` and `TapBranch` tags hash differently. -/
theorem BitcoinTapSoundness.tapleaf_ne_tapbranch :
    BitcoinSer.sha256 (BitcoinSig.ascii "TapLeaf") ≠ BitcoinSer.sha256 (BitcoinSig.ascii "TapBranch") := by
  decide +kernel

/-- A leaf hash equal to a branch hash is a SHA-256 collision. -/
theorem BitcoinTapSoundness.leaf_ne_branch (v : BitcoinSer.Byte) (s a b : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tapleafHash v s = BitcoinTaproot.tapbranchHash a b) : BitcoinTapSoundness.Sha256Collision := by
  simp only [tapleafHash, tapbranchHash] at h
  rcases BitcoinTapSoundness.tagged_collision _ _ _ _ h with ⟨ht, -⟩ | hc
  · exact absurd ht BitcoinTapSoundness.tapleaf_ne_tapbranch
  · exact hc

/-- Equal branch hashes of 32-byte children have the same two children (in some order), or exhibit
a collision. -/
theorem BitcoinTapSoundness.branch_eq (a b c d : BitcoinSer.Bytes) (ha : a.length = 32) (hb : b.length = 32)
    (hc : c.length = 32) (hd : d.length = 32) (h : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash c d) :
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∨ BitcoinTapSoundness.Sha256Collision := by
  simp only [tapbranchHash] at h
  rcases BitcoinTapSoundness.tagged_collision _ _ _ _ h with ⟨-, hm⟩ | hcol
  · left
    split at hm <;> split at hm
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [ha, hc]) hm; exact Or.inl ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [ha, hd]) hm; exact Or.inr ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [hb, hc]) hm; exact Or.inr ⟨h2, h1⟩
    · obtain ⟨h1, h2⟩ := append_inj_len _ _ _ _ (by rw [hb, hd]) hm; exact Or.inl ⟨h2, h1⟩
  · right; exact hcol

/-! ### Trees -/

private theorem hash_length (T : TapTree) : T.hash.length = 32 := by
  cases T <;> simp [TapTree.hash, tapleafHash, tapbranchHash, tagged, BitcoinSig.taggedHash, BitcoinSer.sha256_length]

private theorem leaf_mem_leaves : ∀ (T : TapTree) (d : Nat) (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes),
    TapTree.leaf v s ∈ T.subtreesAt d → tapleafHash v s ∈ T.leaves
  | T, 0, v, s, h => by
    simp only [TapTree.subtreesAt, List.mem_singleton] at h
    subst h; simp [TapTree.leaves]
  | .leaf _ _, d + 1, v, s, h => by simp [TapTree.subtreesAt] at h
  | .branch l r, d + 1, v, s, h => by
    simp only [TapTree.subtreesAt, List.mem_append] at h
    simp only [TapTree.leaves, List.mem_append]
    rcases h with h | h
    · exact Or.inl (leaf_mem_leaves l d v s h)
    · exact Or.inr (leaf_mem_leaves r d v s h)

private theorem branch_children_mem : ∀ (T : TapTree) (d : Nat) (l r : TapTree),
    TapTree.branch l r ∈ T.subtreesAt d → l ∈ T.subtreesAt (d + 1) ∧ r ∈ T.subtreesAt (d + 1)
  | T, 0, l, r, h => by
    simp only [TapTree.subtreesAt, List.mem_singleton] at h
    subst h; simp [TapTree.subtreesAt]
  | .leaf _ _, d + 1, l, r, h => by simp [TapTree.subtreesAt] at h
  | .branch a b, d + 1, l, r, h => by
    simp only [TapTree.subtreesAt, List.mem_append] at h ⊢
    rcases h with h | h
    · have := branch_children_mem a d l r h; exact ⟨Or.inl this.1, Or.inl this.2⟩
    · have := branch_children_mem b d l r h; exact ⟨Or.inr this.1, Or.inr this.2⟩

private theorem path_lands_aux (T : TapTree) :
    ∀ (nodes : List BitcoinSer.Bytes) (h : BitcoinSer.Bytes), (∀ n ∈ nodes, n.length = 32) → h.length = 32 →
    nodes.foldl tapbranchHash h = T.hash →
    (∃ U ∈ T.subtreesAt nodes.length, U.hash = h) ∨ Sha256Collision
  | [], h, _, _, heq => Or.inl ⟨T, by simp [TapTree.subtreesAt], heq.symm⟩
  | n :: rest, h, hn, hh, heq => by
    simp only [List.foldl_cons] at heq
    have hn' : ∀ m ∈ rest, m.length = 32 := fun m hm => hn m (List.mem_cons_of_mem _ hm)
    have hbl : (tapbranchHash h n).length = 32 := by
      simp [tapbranchHash, tagged, BitcoinSig.taggedHash, BitcoinSer.sha256_length]
    rcases path_lands_aux T rest _ hn' hbl heq with ⟨U, hU, hUh⟩ | hc
    · cases U with
      | leaf v s =>
        exact Or.inr (BitcoinTapSoundness.leaf_ne_branch v s h n hUh)
      | branch l r =>
        simp only [TapTree.hash] at hUh
        rcases BitcoinTapSoundness.branch_eq _ _ _ _ (hash_length l) (hash_length r) hh (hn n (List.mem_cons_self ..)) hUh
          with ⟨⟨h1, -⟩ | ⟨-, h2⟩⟩ | hc
        · obtain ⟨hl, -⟩ := branch_children_mem T rest.length l r hU
          exact Or.inl ⟨l, by simpa [List.length_cons] using hl, h1⟩
        · obtain ⟨-, hr⟩ := branch_children_mem T rest.length l r hU
          exact Or.inl ⟨r, by simpa [List.length_cons] using hr, h2⟩
        · exact Or.inr hc
    · exact Or.inr hc

/-- Following a Merkle path of 32-byte nodes from a 32-byte hash to the root of a tree lands on a
subtree at the path's depth, or exhibits a collision. -/
theorem BitcoinTapSoundness.path_lands (T : BitcoinTapSoundness.TapTree) (nodes : List BitcoinSer.Bytes) (h : BitcoinSer.Bytes)
    (hn : ∀ n ∈ nodes, n.length = 32) (hh : h.length = 32) (heq : nodes.foldl BitcoinTaproot.tapbranchHash h = T.hash) :
    (∃ U ∈ T.subtreesAt nodes.length, U.hash = h) ∨ BitcoinTapSoundness.Sha256Collision :=
  path_lands_aux T nodes h hn hh heq

/-- The path nodes of a well-sized control block are 32 bytes each. -/
private theorem controlNodes_len (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = TAPROOT_CONTROL_BASE_SIZE + TAPROOT_CONTROL_NODE_SIZE * k) :
    ∀ n ∈ controlNodes control, n.length = 32 := by
  simp only [controlNodes, TAPROOT_CONTROL_BASE_SIZE, TAPROOT_CONTROL_NODE_SIZE] at hc ⊢
  have hk : (control.length - 33) / 32 = k := by rw [hc]; omega
  rw [hk]
  have hlen : (control.drop 33).length = 32 * k := by simp [List.length_drop, hc]
  generalize control.drop 33 = s at hlen
  clear hc hk
  induction k generalizing s with
  | zero => intro n hn; simp [controlNodes.go] at hn
  | succ k ih =>
    intro n hn
    simp only [controlNodes.go, List.mem_cons] at hn
    rcases hn with hn | hn
    · subst hn; simp only [List.length_take, hlen, TAPROOT_CONTROL_NODE_SIZE]; omega
    · exact ih (s.drop 32) (by simp only [List.length_drop, hlen, TAPROOT_CONTROL_NODE_SIZE]; omega) n hn

/-- **Script-path soundness (Merkle level).** A control block whose Merkle path carries the leaf
hash of `(v, s)` to the root of a tree `T` opens a leaf of `T`, or exhibits a SHA-256 collision. -/
theorem BitcoinTapSoundness.script_path_soundness (T : BitcoinTapSoundness.TapTree) (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) = T.hash) :
    BitcoinTaproot.tapleafHash v s ∈ T.leaves ∨ BitcoinTapSoundness.Sha256Collision := by
  simp only [taprootMerkleRoot] at h
  have hl : (tapleafHash v s).length = 32 := by simp [tapleafHash, tagged, BitcoinSig.taggedHash, BitcoinSer.sha256_length]
  rcases BitcoinTapSoundness.path_lands T (controlNodes control) _ (controlNodes_len control k hc) hl h with ⟨U, hU, hUh⟩ | hcol
  · cases U with
    | leaf v' s' =>
      simp only [TapTree.hash] at hUh
      rw [← hUh]; exact Or.inl (leaf_mem_leaves T _ v' s' hU)
    | branch l r =>
      simp only [TapTree.hash] at hUh
      exact Or.inr (BitcoinTapSoundness.leaf_ne_branch v s _ _ hUh.symm)
  · exact Or.inr hcol

/-- **Script-path soundness (commitment level).** If an output key `q` was honestly built from an
internal key and a tree `T`, then any control block with that internal key and parity that passes
`VerifyTaprootCommitment` for the leaf `(v, s)` opens a leaf of `T`, or exhibits a SHA-256
collision, or exhibits two different tweak scalars carrying the internal point to `q`. -/
theorem BitcoinTapSoundness.commitment_soundness (q internal32 : BitcoinSer.Bytes) (parity : Bool)
    (T : BitcoinTapSoundness.TapTree) (hT : BitcoinTapSoundness.HonestOutput q internal32 parity T)
    (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (hkey : BitcoinTapSoundness.controlInternalKey control = internal32) (hpar : BitcoinTapSoundness.controlParity control = parity)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.verifyTaprootCommitment control q (BitcoinTaproot.tapleafHash v s) = true) :
    BitcoinTaproot.tapleafHash v s ∈ T.leaves ∨ BitcoinTapSoundness.Sha256Collision ∨
      ∃ P, BitcoinSig.liftX (BitcoinSig.beVal internal32) = some P ∧ BitcoinTapSoundness.TweakCollision q parity P := by
  simp only [verifyTaprootCommitment] at h
  rw [show (control.drop 1).take 32 = internal32 from hkey] at h
  rw [show decide ((control.getD 0 0).toNat % 2 = 1) = parity from hpar] at h
  simp only [HonestOutput, checkTapTweak] at hT h
  cases hP : BitcoinSig.liftX (BitcoinSig.beVal internal32) with
  | none => rw [hP] at hT; cases hT
  | some P =>
    rw [hP] at hT h
    by_cases hroot : taprootMerkleRoot control (tapleafHash v s) = T.hash
    · rcases BitcoinTapSoundness.script_path_soundness T control k hc v s hroot with hm | hcol
      · exact Or.inl hm
      · exact Or.inr (Or.inl hcol)
    · -- different roots: equal tweak scalars would be a collision of TapTweak; different ones a tweak collision
      by_cases htw : tapTweakHash internal32 (taprootMerkleRoot control (tapleafHash v s)) = tapTweakHash internal32 T.hash
      · simp only [tapTweakHash] at htw
        rcases BitcoinTapSoundness.tagged_collision _ _ _ _ htw with ⟨-, hm⟩ | hcol
        · exfalso; apply hroot
          exact (append_inj_len _ _ _ _ rfl hm).2
        · exact Or.inr (Or.inl hcol)
      · exact Or.inr (Or.inr ⟨P, rfl, _, _, htw, h, hT⟩)
