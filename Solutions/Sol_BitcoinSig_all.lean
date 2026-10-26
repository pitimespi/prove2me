import Definitions.Def_BitcoinSig
import Theorems.Thm_BitcoinScript_p2pkh_correct

open BitcoinSig BitcoinSer

/-! ### The SIGHASH_SINGLE bug -/

/-- With `SIGHASH_SINGLE` and no output at the input's index, the legacy sighash is `uint256::ONE`. -/
theorem BitcoinSig.sigHash_single_bug (scriptCode : Bytes) (tx : Tx) (nIn hashType : Nat)
    (h1 : hashType &&& 0x1f = BitcoinSig.SIGHASH_SINGLE) (h2 : tx.vout.length ≤ nIn) :
    BitcoinSig.sigHashLegacy scriptCode tx nIn hashType = BitcoinSig.uint256One := by
  unfold sigHashLegacy
  rw [if_pos ⟨h1, h2⟩]

/-! ### What the signature hashes depend on -/

private def skel (i : TxIn) : OutPoint × Nat := (i.prevout, i.nSequence)
private def dflt : TxIn := ⟨⟨[], 0⟩, [], 0, []⟩

private theorem getD_prevout (vin : List TxIn) (k : Nat) :
    (vin.getD k dflt).prevout = ((vin.map skel).getD k (skel dflt)).1 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vin[k]? <;> rfl

private theorem getD_seq (vin : List TxIn) (k : Nat) :
    (vin.getD k dflt).nSequence = ((vin.map skel).getD k (skel dflt)).2 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vin[k]? <;> rfl

private theorem skel_getD (vin vin' : List TxIn) (hv : vin'.map skel = vin.map skel) (j : Nat) :
    (vin'.getD j dflt).prevout = (vin.getD j dflt).prevout ∧
    (vin'.getD j dflt).nSequence = (vin.getD j dflt).nSequence := by
  constructor
  · rw [getD_prevout, getD_prevout, hv]
  · rw [getD_seq, getD_seq, hv]

private theorem serSigInput_skel (tx tx' : Tx) (h : BitcoinSig.sameSkeleton tx tx') (sc : Bytes) (nIn : Nat)
    (a s z : Bool) :
    serSigInput tx' sc nIn a s z = serSigInput tx sc nIn a s z := by
  obtain ⟨_, _, _, hv⟩ := h
  have hv' : tx'.vin.map skel = tx.vin.map skel := hv
  funext k
  unfold serSigInput
  have e := skel_getD tx.vin tx'.vin hv'
  simp only [show (⟨⟨[], 0⟩, [], 0, []⟩ : TxIn) = dflt from rfl, (e _).1, (e _).2]

private theorem serSigTx_skel (tx tx' : Tx) (h : BitcoinSig.sameSkeleton tx tx') (sc : Bytes) (nIn ht : Nat) :
    serSigTx tx' sc nIn ht = serSigTx tx sc nIn ht := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlen : tx'.vin.length = tx.vin.length := by
    have := congrArg List.length h4; simpa using this
  have ho : serSigOutput tx' nIn = serSigOutput tx nIn := by
    funext s k; simp [serSigOutput, h2]
  unfold serSigTx
  dsimp only
  rw [h1, h2, h3, hlen, serSigInput_skel tx tx' ⟨h1, h2, h3, h4⟩, ho]

/-- The legacy signature hash never depends on scriptSigs or witnesses: it is the same for any two
transactions with the same skeleton. -/
theorem BitcoinSig.sigHashLegacy_skeleton (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by
  unfold sigHashLegacy
  rw [h.2.1, serSigTx_skel tx tx' h]

/-- With `SIGHASH_ANYONECANPAY` the legacy hash depends on the signed input alone (plus version,
outputs and lock time). -/
theorem BitcoinSig.sigHashLegacy_anyoneCanPay (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat)
    (hacp : hashType &&& BitcoinSig.SIGHASH_ANYONECANPAY ≠ 0)
    (h1 : tx'.version = tx.version) (h2 : tx'.vout = tx.vout) (h3 : tx'.nLockTime = tx.nLockTime)
    (h4 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).prevout)
    (h5 : (tx'.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence = (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence) :
    BitcoinSig.sigHashLegacy scriptCode tx' nIn hashType = BitcoinSig.sigHashLegacy scriptCode tx nIn hashType := by
  have hs : serSigTx tx' scriptCode nIn hashType = serSigTx tx scriptCode nIn hashType := by
    have ho : serSigOutput tx' nIn = serSigOutput tx nIn := by
      funext s k; simp [serSigOutput, h2]
    have hi : ∀ s z, serSigInput tx' scriptCode nIn true s z 0 = serSigInput tx scriptCode nIn true s z 0 := by
      intro s z; unfold serSigInput; dsimp only; simp only [ite_true]; rw [h4, h5]
    unfold serSigTx
    dsimp only
    have hd : decide (hashType &&& SIGHASH_ANYONECANPAY ≠ 0) = true := decide_eq_true hacp
    rw [h1, h2, h3, ho, hd]
    simp only [ite_true, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, hi]
  unfold sigHashLegacy
  rw [h2, hs]

/-- The BIP143 hash never depends on scriptSigs or witnesses either. -/
theorem BitcoinSig.sigHashWitnessV0_skeleton (scriptCode : Bytes) (tx tx' : Tx) (nIn hashType : Nat) (amount : Int)
    (h : BitcoinSig.sameSkeleton tx tx') :
    BitcoinSig.sigHashWitnessV0 scriptCode tx' nIn hashType amount =
      BitcoinSig.sigHashWitnessV0 scriptCode tx nIn hashType amount := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : tx'.vin.flatMap (fun i => serOutPoint i.prevout) = tx.vin.flatMap (fun i => serOutPoint i.prevout) := by
    have := congrArg (fun l => l.flatMap (fun q : OutPoint × Nat => serOutPoint q.1)) h4
    simpa [List.flatMap_map] using this
  have e2 : tx'.vin.flatMap (fun i => ser32 i.nSequence) = tx.vin.flatMap (fun i => ser32 i.nSequence) := by
    have := congrArg (fun l => l.flatMap (fun q : OutPoint × Nat => ser32 q.2)) h4
    simpa [List.flatMap_map] using this
  have e := skel_getD tx.vin tx'.vin h4 nIn
  unfold sigHashWitnessV0
  simp only [h1, h2, h3, e1, e2, show (⟨⟨[], 0⟩, [], 0, []⟩ : TxIn) = dflt from rfl, e.1, e.2]

/-! ### Keys, signatures, and the checker -/

theorem BitcoinSig.pubkeyValid_iff (pk : Bytes) :
    BitcoinSig.pubkeyValid pk = true ↔
      (pk.length = 33 ∧ ((pk.getD 0 0).toNat = 2 ∨ (pk.getD 0 0).toNat = 3)) ∨
      (pk.length = 65 ∧ ((pk.getD 0 0).toNat = 4 ∨ (pk.getD 0 0).toNat = 6 ∨ (pk.getD 0 0).toNat = 7)) := by
  cases pk with
  | nil => simp [pubkeyValid]
  | cons h t =>
    by_cases h23 : h.toNat = 2 ∨ h.toNat = 3 <;> by_cases h467 : h.toNat = 4 ∨ h.toNat = 6 ∨ h.toNat = 7 <;>
      simp [pubkeyValid, pubkeyLen, h23, h467] <;> omega

/-- A normalized S value is never high. -/
theorem BitcoinSig.normalizeS_low (s : Nat) (hs : s < BitcoinSig.n) :
    BitcoinSig.isHighS (BitcoinSig.normalizeS s) = false := by
  unfold normalizeS isHighS
  unfold BitcoinSig.n at *
  by_cases h : 115792089237316195423570985008687907852837564279074904382605163141518161494337 / 2 < s
  · rw [if_pos (by simpa using h)]; simp; omega
  · rw [if_neg (by simpa using h)]; simp; omega

/-- An overflowed lax parse (the zero signature) never verifies. -/
theorem BitcoinSig.overflow_rejected (pk hash sig : Bytes) (h : BitcoinSig.parseDerLax sig = some (0, 0)) :
    BitcoinSig.pubkeyVerify pk hash sig = false := by
  unfold pubkeyVerify
  split
  · rfl
  · split
    · rfl
    · rw [h]; simp [normalizeS, isHighS, ecdsaVerifyRaw]

/-- An empty signature passes the encoding checks and is rejected by the checker: `some false`. -/
theorem BitcoinSig.checkSig_empty (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode pk : Bytes) (hpk : BitcoinSig.checkPubKeyEncoding f v pk = true) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount v scriptCode [] pk = some false := by
  unfold checkSigPreTapscript
  simp only [checkSignatureEncoding, List.isEmpty_nil, ite_true, Bool.not_true, hpk, Bool.false_eq_true,
    or_self, ite_false, checkECDSASignature, List.getLast?_nil]
  split <;> rfl

/-- With `DERSIG` a non-empty signature that is not strict DER fails the script. -/
theorem BitcoinSig.checkSig_dersig (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode sig pk : Bytes) (hf : f.dersig = true) (hne : sig ≠ [])
    (hder : BitcoinSig.isValidSignatureEncoding sig = false) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount v scriptCode sig pk = none := by
  unfold checkSigPreTapscript
  have : checkSignatureEncoding f sig = false := by
    unfold checkSignatureEncoding
    rw [if_neg (by simpa using hne)]
    simp [hf, hder]
  simp [this]

/-- The legacy checker, unfolded: the two encoding checks, a valid key, a non-empty signature whose
last byte is the hash type, and `CPubKey::Verify` on the legacy sighash of the script code with
the signature push deleted. -/
theorem BitcoinSig.checkSig_base_iff (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int)
    (scriptCode sig pk : Bytes) :
    BitcoinSig.checkSigPreTapscript f tx nIn amount .base scriptCode sig pk = some true ↔
      BitcoinSig.checkSignatureEncoding f sig = true ∧ BitcoinSig.checkPubKeyEncoding f .base pk = true ∧
      BitcoinSig.pubkeyValid pk = true ∧
      ∃ (sig' : Bytes) (ht : Byte), sig = sig' ++ [ht] ∧
        BitcoinSig.pubkeyVerify pk
          (BitcoinSig.sigHashLegacy (BitcoinSig.findAndDelete scriptCode (BitcoinSig.pushBytes sig)).1 tx nIn ht.toNat)
          sig' = true := by
  unfold checkSigPreTapscript
  by_cases he : checkSignatureEncoding f sig = true
  · by_cases hp : checkPubKeyEncoding f .base pk = true
    · simp only [he, hp, Bool.not_true, Bool.false_eq_true, or_self, ite_false, Option.some.injEq, true_and]
      unfold checkECDSASignature
      by_cases hv : pubkeyValid pk = true
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false, true_and]
        cases hl : sig.getLast? with
        | none =>
          simp only [List.getLast?_eq_none_iff] at hl
          subst hl; simp
        | some ht =>
          simp only [show (SigVersion.base = SigVersion.witnessV0) = False by simp, false_and, ite_false]
          constructor
          · intro hpv
            obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hl
            exact ⟨ys, ht, rfl, by rw [List.dropLast_concat] at hpv; exact hpv⟩
          · rintro ⟨sig', ht', rfl, hpv⟩
            have e : ht' = ht := by
              rw [List.getLast?_append, List.getLast?_singleton] at hl
              simpa using hl
            subst e
            rw [List.dropLast_concat]; exact hpv
      · simp only [Bool.not_eq_true] at hv
        simp [hv]
    · simp only [Bool.not_eq_true] at hp
      simp [hp]
  · simp only [Bool.not_eq_true] at he
    simp [he]

/-! ### Byte-level scripts -/

/-- Parsing the P2PKH output script bytes yields the interpreter's `p2pkhScript`. -/
theorem BitcoinSig.parseScript_p2pkh (h : Bytes) (hh : h.length = 20) :
    BitcoinSig.parseScript (BitcoinSig.p2pkhBytes h) = some (BitcoinScript.p2pkhScript h) := by
  have hp : pushBytes h = BitVec.ofNat 8 20 :: h := by
    unfold pushBytes; rw [if_pos (by rw [hh]; decide)]; rw [hh]
  unfold parseScript p2pkhBytes
  rw [hp]
  have hl : ([0x76, 0xa9] ++ (BitVec.ofNat 8 20 :: h) ++ [0x88, 0xac]).length = 25 := by simp [hh]
  rw [hl]
  have ht : (h ++ [0x88, 0xac]).take 20 = h := List.take_left' hh
  have hd : (h ++ [0x88, 0xac]).drop 20 = [0x88, 0xac] := List.drop_left' hh
  simp [parseScriptAux, getOp, OP_PUSHDATA1, OP_PUSHDATA4, ht, hd, hh, BitcoinScript.p2pkhScript]
  decide

/-! ### Strict DER -/

private theorem getD_app_lt {α : Type} (a b : List α) (i : Nat) (d : α) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_app_ge {α : Type} (a b : List α) (i : Nat) (d : α) (h : a.length ≤ i) :
    (a ++ b).getD i d = b.getD (i - a.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- The DER layout encodes validly whenever both integers are minimal and the total fits. -/
theorem BitcoinSig.derEncode_valid (r s : Bytes) (ht : Byte) (hr : BitcoinSig.minimalInt r)
    (hs : BitcoinSig.minimalInt s) (hlen : r.length + s.length ≤ 66) :
    BitcoinSig.isValidSignatureEncoding (BitcoinSig.derEncode r s ht) = true := by
  obtain ⟨hr0, hr1, hr2⟩ := hr
  obtain ⟨hs0, hs1, hs2⟩ := hs
  have hrl : 1 ≤ r.length := List.length_pos_iff.2 hr0
  have hsl : 1 ≤ s.length := List.length_pos_iff.2 hs0
  -- the layout, right-associated
  have hsig : derEncode r s ht =
      [0x30, BitVec.ofNat 8 (r.length + s.length + 4), 0x02, BitVec.ofNat 8 r.length] ++
        (r ++ ([0x02, BitVec.ofNat 8 s.length] ++ (s ++ [ht]))) := by
    simp [derEncode]
  rw [hsig]
  generalize hE : ([0x30, BitVec.ofNat 8 (r.length + s.length + 4), 0x02, BitVec.ofNat 8 r.length] ++
        (r ++ ([0x02, BitVec.ofNat 8 s.length] ++ (s ++ [ht]))) : Bytes) = sig
  have hL : sig.length = r.length + s.length + 7 := by rw [← hE]; simp; omega
  have hb3 : (sig.getD 3 0).toNat = r.length := by
    rw [← hE, getD_app_lt _ _ _ _ (by simp)]; simp [BitVec.toNat_ofNat] <;> omega
  have hb1 : (sig.getD 1 0).toNat = r.length + s.length + 4 := by
    rw [← hE, getD_app_lt _ _ _ _ (by simp)]; simp [BitVec.toNat_ofNat] <;> omega
  have hb0 : (sig.getD 0 0).toNat = 0x30 := by rw [← hE, getD_app_lt _ _ _ _ (by simp)]; rfl
  have hb2 : (sig.getD 2 0).toNat = 0x02 := by rw [← hE, getD_app_lt _ _ _ _ (by simp)]; rfl
  have hb4 : (sig.getD 4 0).toNat = (r.getD 0 0).toNat := by
    rw [← hE, getD_app_ge _ _ _ _ (by simp), getD_app_lt _ _ _ _ (by simp <;> omega)]; rfl
  have hb5 : 1 < r.length → (sig.getD 5 0).toNat = (r.getD 1 0).toNat := by
    intro h
    rw [← hE, getD_app_ge _ _ _ _ (by simp), getD_app_lt _ _ _ _ (by simp <;> omega)]; rfl
  have hR4 : (sig.getD (r.length + 4) 0).toNat = 0x02 := by
    rw [← hE, getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_ge _ _ _ _ (by simp <;> omega)]
    simp
  have hR5 : (sig.getD (5 + r.length) 0).toNat = s.length := by
    rw [← hE, getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_ge _ _ _ _ (by simp <;> omega)]
    simp only [List.length_cons, List.length_nil]
    rw [show 5 + r.length - 4 - r.length = 1 by omega]
    simp [BitVec.toNat_ofNat] <;> omega
  have hR6 : (sig.getD (r.length + 6) 0).toNat = (s.getD 0 0).toNat := by
    rw [← hE, getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_ge _ _ _ _ (by simp <;> omega),
      getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_lt _ _ _ _ (by simp <;> omega)]
    simp only [List.length_cons, List.length_nil]
    rw [show r.length + 6 - 4 - r.length - 2 = 0 by omega]
  have hR7 : 1 < s.length → (sig.getD (r.length + 7) 0).toNat = (s.getD 1 0).toNat := by
    intro h
    rw [← hE, getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_ge _ _ _ _ (by simp <;> omega),
      getD_app_ge _ _ _ _ (by simp <;> omega), getD_app_lt _ _ _ _ (by simp <;> omega)]
    simp only [List.length_cons, List.length_nil]
    rw [show r.length + 7 - 4 - r.length - 2 = 1 by omega]
  unfold isValidSignatureEncoding
  dsimp only
  simp only [hL, hb0, hb1, hb2, hb3, hb4, hR4, hR5, hR6]
  repeat' (first
    | rw [if_neg (by omega)]
    | rw [if_neg (by rintro ⟨h1, h2, h3⟩; rw [hb5 h1] at h3; have := hr2 h1 h2; omega)]
    | rw [if_neg (by rintro ⟨h1, h2, h3⟩; rw [hR7 h1] at h3; have := hs2 h1 h2; omega)])

private theorem getD_drop' {α : Type} (l : List α) (k i : Nat) (d : α) : (l.drop k).getD i d = l.getD (k + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem getD_take' {α : Type} (l : List α) (k i : Nat) (d : α) (h : i < k) : (l.take k).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

private theorem take4_eq (l : Bytes) (h : 4 ≤ l.length) :
    l.take 4 = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  match l with
  | a :: b :: c :: d :: _ => rfl
  | [] | [_] | [_, _] | [_, _, _] => simp at h

private theorem take2_eq (l : Bytes) (h : 2 ≤ l.length) : l.take 2 = [l.getD 0 0, l.getD 1 0] := by
  match l with
  | a :: b :: _ => rfl
  | [] | [_] => simp at h

private theorem eq_single (l : Bytes) (h : l.length = 1) : l = [l.getD 0 0] := by
  match l with
  | [a] => rfl
  | [] | _ :: _ :: _ => simp at h

private theorem ofNat_toNat' (b : Byte) : BitVec.ofNat 8 b.toNat = b := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Every signature `IsValidSignatureEncoding` accepts has the DER layout with minimal integers:
the three leading-zero rules are exactly what forces the layout. -/
theorem BitcoinSig.derEncode_complete (sig : Bytes) (h : BitcoinSig.isValidSignatureEncoding sig = true) :
    ∃ (r s : Bytes) (ht : Byte), sig = BitcoinSig.derEncode r s ht ∧ BitcoinSig.minimalInt r ∧
      BitcoinSig.minimalInt s ∧ r.length + s.length ≤ 66 := by
  unfold isValidSignatureEncoding at h
  dsimp only at h
  -- peel the fourteen tests
  by_cases c1 : sig.length < 9
  · rw [if_pos c1] at h; cases h
  rw [if_neg c1] at h
  by_cases c2 : 73 < sig.length
  · rw [if_pos c2] at h; cases h
  rw [if_neg c2] at h
  by_cases c3 : (sig.getD 0 0).toNat ≠ 0x30
  · rw [if_pos c3] at h; cases h
  rw [if_neg c3] at h
  by_cases c4 : (sig.getD 1 0).toNat ≠ sig.length - 3
  · rw [if_pos c4] at h; cases h
  rw [if_neg c4] at h
  by_cases c5 : sig.length ≤ 5 + (sig.getD 3 0).toNat
  · rw [if_pos c5] at h; cases h
  rw [if_neg c5] at h
  by_cases c6 : (sig.getD 3 0).toNat + (sig.getD (5 + (sig.getD 3 0).toNat) 0).toNat + 7 ≠ sig.length
  · rw [if_pos c6] at h; cases h
  rw [if_neg c6] at h
  by_cases c7 : (sig.getD 2 0).toNat ≠ 0x02
  · rw [if_pos c7] at h; cases h
  rw [if_neg c7] at h
  by_cases c8 : (sig.getD 3 0).toNat = 0
  · rw [if_pos c8] at h; cases h
  rw [if_neg c8] at h
  by_cases c9 : 0x80 ≤ (sig.getD 4 0).toNat
  · rw [if_pos c9] at h; cases h
  rw [if_neg c9] at h
  by_cases c10 : 1 < (sig.getD 3 0).toNat ∧ (sig.getD 4 0).toNat = 0 ∧ (sig.getD 5 0).toNat < 0x80
  · rw [if_pos c10] at h; cases h
  rw [if_neg c10] at h
  by_cases c11 : (sig.getD ((sig.getD 3 0).toNat + 4) 0).toNat ≠ 0x02
  · rw [if_pos c11] at h; cases h
  rw [if_neg c11] at h
  by_cases c12 : (sig.getD (5 + (sig.getD 3 0).toNat) 0).toNat = 0
  · rw [if_pos c12] at h; cases h
  rw [if_neg c12] at h
  by_cases c13 : 0x80 ≤ (sig.getD ((sig.getD 3 0).toNat + 6) 0).toNat
  · rw [if_pos c13] at h; cases h
  rw [if_neg c13] at h
  by_cases c14 : 1 < (sig.getD (5 + (sig.getD 3 0).toNat) 0).toNat ∧ (sig.getD ((sig.getD 3 0).toNat + 6) 0).toNat = 0 ∧
      (sig.getD ((sig.getD 3 0).toNat + 7) 0).toNat < 0x80
  · rw [if_pos c14] at h; cases h
  clear h
  -- name the pieces
  generalize hlR : (sig.getD 3 0).toNat = lenR at *
  generalize hlS : (sig.getD (5 + lenR) 0).toNat = lenS at *
  have hlen : sig.length = lenR + lenS + 7 := by omega
  refine ⟨(sig.drop 4).take lenR, (sig.drop (6 + lenR)).take lenS, sig.getD (lenR + lenS + 6) 0, ?_, ?_, ?_, ?_⟩
  · -- the layout: cut `sig` at 4, 4 + lenR, 6 + lenR, 6 + lenR + lenS
    have e1 : sig = sig.take 4 ++ sig.drop 4 := (List.take_append_drop 4 sig).symm
    have e2 : sig.drop 4 = (sig.drop 4).take lenR ++ (sig.drop 4).drop lenR := (List.take_append_drop _ _).symm
    have e3 : (sig.drop 4).drop lenR = sig.drop (4 + lenR) := by rw [List.drop_drop]
    have e4 : sig.drop (4 + lenR) = (sig.drop (4 + lenR)).take 2 ++ (sig.drop (4 + lenR)).drop 2 := (List.take_append_drop _ _).symm
    have e5 : (sig.drop (4 + lenR)).drop 2 = sig.drop (6 + lenR) := by rw [List.drop_drop]; congr 1; omega
    have e6 : sig.drop (6 + lenR) = (sig.drop (6 + lenR)).take lenS ++ (sig.drop (6 + lenR)).drop lenS := (List.take_append_drop _ _).symm
    have e7 : (sig.drop (6 + lenR)).drop lenS = sig.drop (6 + lenR + lenS) := by rw [List.drop_drop]
    have e8 : sig.drop (6 + lenR + lenS) = [sig.getD (lenR + lenS + 6) 0] := by
      have := eq_single (sig.drop (6 + lenR + lenS)) (by simp; omega)
      rw [getD_drop'] at this
      rw [this]; congr 2; omega
    have t4 : sig.take 4 = [sig.getD 0 0, sig.getD 1 0, sig.getD 2 0, sig.getD 3 0] := take4_eq sig (by omega)
    have t2 : (sig.drop (4 + lenR)).take 2 = [sig.getD (4 + lenR) 0, sig.getD (4 + lenR + 1) 0] := by
      rw [take2_eq _ (by simp; omega), getD_drop', getD_drop', Nat.add_zero]
    have hr : ((sig.drop 4).take lenR).length = lenR := by simp; omega
    have hs : ((sig.drop (6 + lenR)).take lenS).length = lenS := by simp; omega
    have b0 : sig.getD 0 0 = 0x30 := by
      have := ofNat_toNat' (sig.getD 0 0); rw [show (sig.getD 0 0).toNat = 0x30 by omega] at this; exact this.symm
    have b2 : sig.getD 2 0 = 0x02 := by
      have := ofNat_toNat' (sig.getD 2 0); rw [show (sig.getD 2 0).toNat = 0x02 by omega] at this; exact this.symm
    have b1 : sig.getD 1 0 = BitVec.ofNat 8 (lenR + lenS + 4) := by
      have := ofNat_toNat' (sig.getD 1 0)
      rw [show (sig.getD 1 0).toNat = lenR + lenS + 4 by omega] at this
      exact this.symm
    have b3 : sig.getD 3 0 = BitVec.ofNat 8 lenR := by
      have := ofNat_toNat' (sig.getD 3 0)
      rw [hlR] at this
      exact this.symm
    have bR4 : sig.getD (4 + lenR) 0 = 0x02 := by
      have := ofNat_toNat' (sig.getD (4 + lenR) 0)
      rw [show 4 + lenR = lenR + 4 by omega, show (sig.getD (lenR + 4) 0).toNat = 0x02 by omega] at this
      rw [show 4 + lenR = lenR + 4 by omega]; exact this.symm
    have bR5 : sig.getD (4 + lenR + 1) 0 = BitVec.ofNat 8 lenS := by
      have := ofNat_toNat' (sig.getD (4 + lenR + 1) 0)
      rw [show 4 + lenR + 1 = 5 + lenR by omega, hlS] at this
      rw [show 4 + lenR + 1 = 5 + lenR by omega]; exact this.symm
    unfold derEncode
    rw [hr, hs]
    conv => lhs; rw [e1, t4, e2, e3, e4, t2, e5, e6, e7, e8, b0, b1, b2, b3, bR4, bR5]
    simp
  · refine ⟨?_, ?_, ?_⟩
    · intro hnil
      have := congrArg List.length hnil
      simp at this; omega
    · rw [getD_take' _ _ _ _ (by omega), getD_drop', Nat.add_zero]; omega
    · intro h1 h2
      simp only [List.length_take, List.length_drop] at h1
      rw [getD_take' _ _ _ _ (by omega), getD_drop', Nat.add_zero] at h2
      rw [getD_take' _ _ _ _ (by omega), getD_drop', show (4:Nat) + 1 = 5 from rfl]
      omega
  · refine ⟨?_, ?_, ?_⟩
    · intro hnil
      have := congrArg List.length hnil
      simp at this; omega
    · rw [getD_take' _ _ _ _ (by omega), getD_drop', Nat.add_zero, show 6 + lenR = lenR + 6 by omega]; omega
    · intro h1 h2
      simp only [List.length_take, List.length_drop] at h1
      rw [getD_take' _ _ _ _ (by omega), getD_drop', Nat.add_zero, show 6 + lenR = lenR + 6 by omega] at h2
      rw [getD_take' _ _ _ _ (by omega), getD_drop', show 6 + lenR + 1 = lenR + 7 by omega]
      omega
  · simp only [List.length_take, List.length_drop]; omega

/-! ### The goal: P2PKH against the concrete checker -/

/-- `VerifyScript` for P2PKH with Core's hashes and signature checker: success iff the key hashes to
the committed value and the pre-tapscript signature check on the output script accepts. -/
theorem BitcoinSig.p2pkh_concrete (f : SigFlags) (fl : BitcoinScript.Flags) (tx : Tx) (nIn : Nat) (amount : Int)
    (v : SigVersion) (sig pk h : Bytes)
    (hsig : sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hpk : pk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hh : h.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.verifyScriptPlain fl (BitcoinSig.legacyOracle f tx nIn amount v (BitcoinSig.p2pkhBytes h))
        [.push sig, .push pk] (BitcoinScript.p2pkhScript h) = true ↔
      BitcoinSer.hash160 pk = h ∧
      BitcoinSig.checkSigPreTapscript f tx nIn amount v (BitcoinSig.p2pkhBytes h) sig pk = some true :=
  BitcoinScript.p2pkh_correct fl (legacyOracle f tx nIn amount v (p2pkhBytes h)) sig pk h hsig hpk hh
