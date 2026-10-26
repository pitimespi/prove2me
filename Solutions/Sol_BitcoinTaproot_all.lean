import Definitions.Def_BitcoinTaproot

open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

/-! ### Branch hashes and merkle paths -/

private theorem lexLt_asymm : ∀ (a b : Bytes), lexLt a b = true → lexLt b a = false
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [lexLt] at h
  | x :: xs, y :: ys, h => by
    simp only [lexLt] at h ⊢
    by_cases h1 : x.toNat < y.toNat
    · rw [if_neg (by omega), if_pos h1]
    · rw [if_neg h1] at h
      by_cases h2 : y.toNat < x.toNat
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        rw [if_neg h2, if_neg h1]
        exact lexLt_asymm xs ys h

private theorem lexLt_total : ∀ (a b : Bytes), lexLt a b = false → lexLt b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [lexLt] at h
  | _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [lexLt] at h1 h2
    by_cases hxy : x.toNat < y.toNat
    · rw [if_pos hxy] at h1; cases h1
    · rw [if_neg hxy] at h1
      by_cases hyx : y.toNat < x.toNat
      · rw [if_pos hyx] at h2; cases h2
      · rw [if_neg hyx] at h1
        rw [if_neg hyx, if_neg hxy] at h2
        have hx : x = y := by
          have : x.toNat = y.toNat := by omega
          exact BitVec.eq_of_toNat_eq this
        rw [hx, lexLt_total xs ys h1 h2]

/-- `ComputeTapbranchHash` is symmetric: the order of the two children does not matter. -/
theorem BitcoinTaproot.tapbranch_comm (a b : Bytes) : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash b a := by
  unfold tapbranchHash
  cases h1 : lexLt a b
  · cases h2 : lexLt b a
    · rw [lexLt_total a b h1 h2]
    · simp
  · rw [lexLt_asymm a b h1]; simp

/-- A control block with no path nodes commits to the leaf itself. -/
theorem BitcoinTaproot.merkleRoot_base (control leaf : Bytes) (h : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot control leaf = leaf := by
  unfold taprootMerkleRoot controlNodes
  rw [h]; simp [controlNodes.go]

/-- Appending a 32-byte node to a control block hashes the current root with that node. -/
theorem BitcoinTaproot.merkleRoot_snoc (control node leaf : Bytes)
    (hc : BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE ≤ control.length)
    (hm : (control.length - BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) % BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE = 0)
    (hn : node.length = BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot (control ++ node) leaf =
      BitcoinTaproot.tapbranchHash (BitcoinTaproot.taprootMerkleRoot control leaf) node := by
  unfold taprootMerkleRoot controlNodes
  unfold TAPROOT_CONTROL_BASE_SIZE TAPROOT_CONTROL_NODE_SIZE at *
  have e1 : ∀ (n : Nat) (t : Bytes), controlNodes.go (n + 1) t = t.take 32 :: controlNodes.go n (t.drop 32) :=
    fun n t => rfl
  have key : ∀ (k : Nat) (s : Bytes), s.length = k * 32 →
      controlNodes.go (k + 1) (s ++ node) = controlNodes.go k s ++ [node] := by
    intro k
    induction k with
    | zero =>
      intro s hs
      have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [e1, List.nil_append, List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
      rfl
    | succ k ih =>
      intro s hs
      rw [e1 (k + 1) (s ++ node), e1 k s]
      have hl : 32 ≤ s.length := by omega
      rw [List.take_append_of_le_length hl, List.drop_append_of_le_length hl, ih (s.drop 32) (by simp; omega)]
      rfl
  simp only [List.length_append, hn]
  rw [show (control.length + 32 - 33) / 32 = (control.length - 33) / 32 + 1 by omega]
  rw [List.drop_append_of_le_length hc]
  rw [key _ _ (by simp; omega)]
  simp [List.foldl_append]

/-! ### Tapscript rules -/

/-- A script whose `OP_SUCCESSx` scan succeeds is accepted outright, whatever the stack or weight. -/
theorem BitcoinTaproot.opsuccess_accepts (c : TapCtx) (ed : ExecData) (stack : List Bytes) (script : Bytes) (weight : Int)
    (h : BitcoinTaproot.opSuccessScan script.length script = some true) :
    BitcoinTaproot.executeTapscript c ed stack script weight = true := by
  unfold executeTapscript; rw [h]

/-- `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` are script errors in Tapscript. -/
theorem BitcoinTaproot.checkmultisig_rejected (c : TapCtx) (ed : ExecData) (fExec : Bool) (ts : TapState) :
    BitcoinTaproot.tapExecOp c ed fExec BitcoinScript.OP_CHECKMULTISIG ts = none ∧
    BitcoinTaproot.tapExecOp c ed fExec BitcoinScript.OP_CHECKMULTISIGVERIFY ts = none := by
  constructor <;> rfl

/-- `MINIMALIF` is consensus: an executed `OP_IF` whose argument is not `[]` or `[1]` fails. -/
theorem BitcoinTaproot.minimalif_rejects (c : TapCtx) (ed : ExecData) (ts : TapState) (top : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = top :: rest) (h : 1 < top.length ∨ (top.length = 1 ∧ (top.getD 0 0).toNat ≠ 1)) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_IF ts = none := by
  unfold tapExecOp
  simp only [BEq.rfl, Bool.true_or, ite_true, hs]
  rw [if_pos h]

/-- The validation-weight budget: an executed `OP_CHECKSIG` with a non-empty signature and fewer than
50 weight units left is a script error, before any signature is checked. -/
theorem BitcoinTaproot.sigops_budget (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey sig : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: sig :: rest) (hsig : sig ≠ []) (hw : ts.weightLeft < BitcoinTaproot.VALIDATION_WEIGHT_PER_SIGOP_PASSED) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts = none := by
  unfold tapExecOp
  rw [if_neg (by decide)]
  simp only [BEq.rfl, Bool.true_or, ite_true, hs]
  unfold evalChecksigTapscript
  have hne : sig.isEmpty = false := by cases sig; exact absurd rfl hsig; rfl
  dsimp only
  simp only [hne, Bool.not_false, ite_true]
  rw [if_pos ⟨trivial, by unfold VALIDATION_WEIGHT_PER_SIGOP_PASSED at *; omega⟩]

/-- An empty signature is a clean `false` (no weight consumed, no key check) for a 32-byte key. -/
theorem BitcoinTaproot.checksig_empty (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: [] :: rest) (hpk : pubkey.length = 32) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts =
      some { ts with st := { ts.st with stack := BitcoinScript.boolBytes false :: rest } } := by
  unfold tapExecOp
  rw [if_neg (by decide)]
  simp only [BEq.rfl, Bool.true_or, ite_true, hs]
  unfold evalChecksigTapscript
  simp [hpk, show ¬ (BitcoinScript.OP_CHECKSIG = BitcoinScript.OP_CHECKSIGVERIFY) by decide]

/-! ### The BIP341 signature hash -/

/-- Only hash types `0..3` and `0x81..0x83` are defined. -/
theorem BitcoinTaproot.sighash_type_invalid (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (h : ¬ (hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83))) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by
  unfold sigHashSchnorr; rw [if_pos h]

/-- `SIGHASH_SINGLE` without a corresponding output fails (no `uint256::ONE` quirk in Taproot). -/
theorem BitcoinTaproot.sighash_single_missing (tx : Tx) (spent : List TxOut) (inPos hashType : Nat) (tapscript : Bool) (ed : ExecData)
    (hv : hashType ≤ 3 ∨ (0x81 ≤ hashType ∧ hashType ≤ 0x83)) (h3 : hashType &&& 3 = 3) (hout : tx.vout.length ≤ inPos) :
    BitcoinTaproot.sigHashSchnorr tx spent inPos hashType tapscript ed = none := by
  unfold sigHashSchnorr
  rw [if_neg (fun hn => hn hv)]
  have hne : hashType ≠ SIGHASH_DEFAULT := by
    unfold SIGHASH_DEFAULT; intro h0; rw [h0] at h3; simp at h3
  dsimp only
  simp only [hne, ite_false, h3, BitcoinSig.SIGHASH_SINGLE, ite_true, hout]

/-! ### Key path, annex, script path -/

/-- The key-path witness `[sig]` carries no annex; the handler is exactly the Schnorr check of the
output key over the BIP341 hash with no annex. -/
theorem BitcoinTaproot.keypath_handler (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig q : Bytes) :
    BitcoinTaproot.taprootHandler spent c [sig] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false ⟨false, [], [], 0xFFFFFFFF⟩ := by
  unfold taprootHandler
  simp [hasAnnex]

/-- With an annex, the key path commits to it: the handler is the Schnorr check with the annex hash. -/
theorem BitcoinTaproot.keypath_annex (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig annex q : Bytes)
    (ha : (annex.getD 0 0).toNat = BitcoinTaproot.ANNEX_TAG) (hne : annex ≠ []) :
    BitcoinTaproot.taprootHandler spent c [sig, annex] q =
      BitcoinTaproot.checkSchnorrSignature c.tx spent c.nIn sig q false
        ⟨true, BitcoinSer.sha256 (BitcoinSer.serBytes annex), [], 0xFFFFFFFF⟩ := by
  unfold taprootHandler
  have h2 : hasAnnex [sig, annex] = true := by
    unfold hasAnnex
    cases annex with
    | nil => exact absurd rfl hne
    | cons b _ => simp only [List.getD_cons_zero] at ha; simp [ha]
  simp [h2]

/-- The Schnorr checker, unfolded: a 64-byte signature with `SIGHASH_DEFAULT`, or a 65-byte one
whose last byte is a non-zero hash type, verifying under BIP340 against the BIP341 hash. -/
theorem BitcoinTaproot.checkSchnorr_iff (tx : Tx) (spent : List TxOut) (nIn : Nat) (sig q : Bytes) (tapscript : Bool) (ed : ExecData) :
    BitcoinTaproot.checkSchnorrSignature tx spent nIn sig q tapscript ed = true ↔
      ∃ (body : Bytes) (ht : Nat) (h : Bytes), body.length = 64 ∧
        ((sig = body ∧ ht = 0) ∨ (∃ b : Byte, sig = body ++ [b] ∧ b.toNat = ht ∧ ht ≠ 0)) ∧
        BitcoinTaproot.sigHashSchnorr tx spent nIn ht tapscript ed = some h ∧
        BitcoinSig.schnorrVerify q h body = true := by
  unfold checkSchnorrSignature
  dsimp only
  by_cases h64 : sig.length = 64
  · rw [if_neg (by omega)]
    simp only [h64, show ¬ ((64:Nat) = 65) by omega, ite_false, false_and, SIGHASH_DEFAULT]
    constructor
    · intro h
      cases hh : sigHashSchnorr tx spent nIn 0 tapscript ed with
      | none => rw [hh] at h; cases h
      | some hv => rw [hh] at h; exact ⟨sig, 0, hv, h64, Or.inl ⟨rfl, rfl⟩, hh, h⟩
    · rintro ⟨body, ht, hv, hl, hd, hh, hs⟩
      rcases hd with ⟨rfl, rfl⟩ | ⟨b, rfl, _, _⟩
      · rw [hh]; exact hs
      · simp at h64; omega
  · by_cases h65 : sig.length = 65
    · rw [if_neg (by omega)]
      obtain ⟨body, b, rfl⟩ : ∃ body b, sig = body ++ [b] := by
        match sig, h65 with
        | [], h => simp at h
        | s :: ss, _ => exact ⟨(s :: ss).dropLast, (s :: ss).getLast (by simp), (List.dropLast_concat_getLast _).symm⟩
      have hb65 : body.length = 64 := by simp at h65; omega
      simp only [h65, ite_true, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some,
        List.dropLast_concat, SIGHASH_DEFAULT, true_and]
      constructor
      · intro h
        by_cases hb : b.toNat = 0
        · rw [if_pos hb] at h; cases h
        · rw [if_neg hb] at h
          cases hh : sigHashSchnorr tx spent nIn b.toNat tapscript ed with
          | none => rw [hh] at h; cases h
          | some hv =>
            rw [hh] at h
            exact ⟨body, b.toNat, hv, hb65, Or.inr ⟨b, rfl, rfl, hb⟩, hh, h⟩
      · rintro ⟨s2, ht, hv, hl, hd, hh, hs⟩
        rcases hd with ⟨he, rfl⟩ | ⟨b2, he, hbt, hne⟩
        · have := congrArg List.length he; simp at this; omega
        · have e := List.append_inj_right he (by omega)
          have e2 := List.append_inj_left he (by omega)
          simp only [List.cons.injEq, and_true] at e
          subst e; subst e2
          rw [if_neg (by rw [hbt]; exact hne), hbt, hh]; exact hs
    · rw [if_pos ⟨h64, h65⟩]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨body, ht, hv, hl, hd, _, _⟩
      rcases hd with ⟨rfl, _⟩ | ⟨b, rfl, _, _⟩
      · exact h64 hl
      · simp at h65; omega

/-- **Taproot key-path spending is correct.** The output `OP_1 <q>` spent with the single witness
element `sig` verifies, under the Taproot flag, iff `sig` is a 64-byte BIP340 signature by `q` of the
BIP341 hash under `SIGHASH_DEFAULT`, or a 65-byte one under the non-zero hash type of its last byte. -/
theorem BitcoinTaproot.keypath_correct (spent : List TxOut) (c : BitcoinVerify.Ctx) (sig q : Bytes) :
    BitcoinTaproot.taprootHandler spent c [sig] q = true ↔
      ∃ (body : Bytes) (ht : Nat) (h : Bytes), body.length = 64 ∧
        ((sig = body ∧ ht = 0) ∨ (∃ b : Byte, sig = body ++ [b] ∧ b.toNat = ht ∧ ht ≠ 0)) ∧
        BitcoinTaproot.sigHashSchnorr c.tx spent c.nIn ht false ⟨false, [], [], 0xFFFFFFFF⟩ = some h ∧
        BitcoinSig.schnorrVerify q h body = true := by
  rw [BitcoinTaproot.keypath_handler]
  exact BitcoinTaproot.checkSchnorr_iff _ _ _ _ _ _ _

/-- A script-path spend that verifies has a valid commitment: the control block's merkle path from the
leaf hash of the revealed script, tweaked into the internal key, is the output key. -/
theorem BitcoinTaproot.scriptpath_commitment (spent : List TxOut) (c : BitcoinVerify.Ctx) (stack : List Bytes)
    (script control q : Bytes) (hna : BitcoinTaproot.hasAnnex (stack ++ [script, control]) = false)
    (h : BitcoinTaproot.taprootHandler spent c (stack ++ [script, control]) q = true) :
    BitcoinTaproot.verifyTaprootCommitment control q
      (BitcoinTaproot.tapleafHash (BitVec.ofNat 8 ((control.getD 0 0).toNat &&& BitcoinTaproot.TAPROOT_LEAF_MASK)) script) = true := by
  have e : stack ++ [script, control] = (stack ++ [script]) ++ [control] := by simp
  rw [e] at h
  unfold taprootHandler at h
  rw [e] at hna
  simp only [hna, Bool.false_eq_true, ite_false] at h
  have hne : ((stack ++ [script]) ++ [control]).isEmpty = false := by simp
  have hlen : ((stack ++ [script]) ++ [control]).length ≠ 1 := by simp
  simp only [hne, Bool.false_eq_true, ite_false, hlen] at h
  simp only [List.getLast?_concat, List.dropLast_concat] at h
  (try dsimp only at h)
  by_cases hcom : verifyTaprootCommitment control q
      (tapleafHash (BitVec.ofNat 8 ((control.getD 0 0).toNat &&& TAPROOT_LEAF_MASK)) script) = true
  · exact hcom
  · simp only [Bool.not_eq_true] at hcom
    split at h
    · cases h
    · rw [hcom] at h
      simp at h
