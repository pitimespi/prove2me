import Definitions.Def_BitcoinScriptV2

open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

set_option linter.unusedSimpArgs false

/-! ### The published oracle is the V2 oracle on the whole script -/

theorem BitcoinScriptV2.legacyOracle_eq (f : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : BitcoinScript.Bytes) :
    BitcoinSig.legacyOracle f tx nIn amount v sc =
      BitcoinScriptV2.withCodeSig (BitcoinScriptV2.legacyOracleV2 f tx nIn amount v) v sc := by
  rfl

private theorem annotateAux_parse : ∀ (n : Nat) (s : BitcoinScript.Bytes),
    (annotateAux n s).map (List.map Prod.fst) = parseScriptAux n s
  | _, [] => by cases ‹Nat› <;> simp [annotateAux, parseScriptAux]
  | 0, _ :: _ => by simp [annotateAux, parseScriptAux]
  | n + 1, b :: s => by
    simp only [annotateAux, parseScriptAux]
    cases getOp (b :: s) with
    | none => rfl
    | some ir =>
      obtain ⟨i, r⟩ := ir
      have ih := annotateAux_parse n r
      cases h : annotateAux n r with
      | none => simp only [h, Option.map_none] at ih; simp [h, ← ih]
      | some l => simp only [h, Option.map_some] at ih; simp [h, ← ih]

theorem BitcoinScriptV2.annotate_parse (s : BitcoinScript.Bytes) :
    (BitcoinScriptV2.annotate s).map (List.map Prod.fst) = BitcoinSig.parseScript s := by
  exact annotateAux_parse s.length s

/-- `getOp` on a non-push opcode consumes exactly one byte. -/
private theorem getOp_op (s r : BitcoinScript.Bytes) (c : BitcoinScript.Byte) (h : getOp s = some (.op c, r)) :
    s = c :: r := by
  cases s with
  | nil => simp [getOp] at h
  | cons b rest =>
    simp only [getOp] at h
    split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
    · simp at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2; rfl

/-- `getOp` returns a suffix of its input. -/
private theorem getOp_suffix (s r : BitcoinScript.Bytes) (i : Instr) (h : getOp s = some (i, r)) :
    ∃ pre, s = pre ++ r := by
  cases s with
  | nil => simp [getOp] at h
  | cons b rest =>
    simp only [getOp] at h
    split at h
    · split at h
      · simp at h
      · next sz r' hsz =>
          split at h
          · simp at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          -- r' is a suffix of rest
          have hr' : ∃ pre, rest = pre ++ r' := by
            split at hsz
            · simp at hsz; obtain ⟨_, rfl⟩ := hsz; exact ⟨[], rfl⟩
            · split at hsz
              · cases rest with
                | nil => simp at hsz
                | cons x xs => simp at hsz; obtain ⟨_, rfl⟩ := hsz; exact ⟨[x], rfl⟩
              · split at hsz
                · split at hsz
                  · simp at hsz
                  · simp at hsz; obtain ⟨_, rfl⟩ := hsz; exact ⟨rest.take 2, (List.take_append_drop 2 rest).symm⟩
                · split at hsz
                  · simp at hsz
                  · simp at hsz; obtain ⟨_, rfl⟩ := hsz; exact ⟨rest.take 4, (List.take_append_drop 4 rest).symm⟩
          obtain ⟨pre, rfl⟩ := hr'
          exact ⟨b :: pre ++ r'.take sz, by simp [List.take_append_drop]⟩
    · simp at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨[b], rfl⟩

/-- every annotated instruction is followed by a suffix of the script; a non-push opcode `c` is the byte
just before its suffix. -/
private theorem annotateAux_suffix : ∀ (n : Nat) (s : BitcoinScript.Bytes) (l : List (Instr × BitcoinScript.Bytes)),
    annotateAux n s = some l → ∀ i r, (i, r) ∈ l → (∃ pre, s = pre ++ r) ∧ (∀ c, i = .op c → ∃ pre, s = pre ++ c :: r)
  | _, [], l, h => by
    cases ‹Nat› <;> simp [annotateAux] at h <;> subst h <;> simp
  | 0, _ :: _, l, h => by simp [annotateAux] at h
  | n + 1, b :: s, l, h => by
    simp only [annotateAux] at h
    cases hg : getOp (b :: s) with
    | none => simp [hg] at h
    | some ir =>
      obtain ⟨i0, r0⟩ := ir
      simp only [hg] at h
      cases ha : annotateAux n r0 with
      | none => simp [ha] at h
      | some l0 =>
        simp only [ha, Option.some.injEq] at h
        subst h
        intro i r hm
        simp only [List.mem_cons, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | hm
        · constructor
          · exact getOp_suffix _ _ _ hg
          · intro c hc
            subst hc
            exact ⟨[], getOp_op _ _ _ hg⟩
        · have ih := annotateAux_suffix n r0 l0 ha i r hm
          obtain ⟨⟨pre, hpre⟩, hop⟩ := ih
          obtain ⟨pre0, hpre0⟩ := getOp_suffix _ _ _ hg
          constructor
          · exact ⟨pre0 ++ pre, by rw [hpre0, hpre, List.append_assoc]⟩
          · intro c hc
            obtain ⟨pre1, hpre1⟩ := hop c hc
            exact ⟨pre0 ++ pre1, by rw [hpre0, hpre1, List.append_assoc]⟩

theorem BitcoinScriptV2.annotate_suffix (s : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (h : BitcoinScriptV2.annotate s = some l) (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes) (hm : (i, r) ∈ l) :
    ∃ pre, s = pre ++ r := by
  exact (annotateAux_suffix s.length s l h i r hm).1

theorem BitcoinScriptV2.annotate_op_suffix (s : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (h : BitcoinScriptV2.annotate s = some l) (c : BitcoinScript.Byte) (r : BitcoinScript.Bytes) (hm : (.op c, r) ∈ l) :
    ∃ p, s[p]? = some c ∧ r = s.drop (p + 1) := by
  obtain ⟨pre, hpre⟩ := (annotateAux_suffix s.length s l h (.op c) r hm).2 c rfl
  refine ⟨pre.length, ?_, ?_⟩
  · rw [hpre]; simp
  · rw [hpre]; simp

/-! ### The multisig branch of `execOp` consults the oracle only on the multisig's signatures -/

private theorem multisigLoop_congr (o o' : Oracle) : ∀ (sigs keys : List Bytes),
    (∀ sig ∈ sigs, ∀ pk, o'.checkSig sig pk = o.checkSig sig pk) →
    multisigLoop o' sigs keys = multisigLoop o sigs keys
  | [], _, _ => by simp [multisigLoop]
  | _ :: _, [], _ => by simp [multisigLoop]
  | sig :: sigs, key :: keys, h => by
    simp only [multisigLoop]
    rw [h sig (by simp) key]
    cases o.checkSig sig key with
    | none => rfl
    | some ok =>
      simp only
      have ih1 := multisigLoop_congr o o' sigs keys (fun s hs pk => h s (by simp [hs]) pk)
      have ih2 := multisigLoop_congr o o' (sig :: sigs) keys h
      rw [ih1, ih2]

private theorem execOp_multisig_congr (f : Flags) (o : Oracle) (cs : Bytes → Bytes → Option Bool) (fExec : Bool)
    (c : Byte) (hc : c = OP_CHECKMULTISIG ∨ c = OP_CHECKMULTISIGVERIFY) (s : State)
    (h : ∀ sig ∈ multisigSigs s.stack, ∀ pk, cs sig pk = o.checkSig sig pk) :
    execOp f { o with checkSig := cs } fExec c s = execOp f o fExec c s := by
  rcases hc with rfl | rfl <;>
  · simp (config := {decide := true}) only [execOp, ↓reduceIte]
    cases hs : s.stack with
    | nil => simp
    | cons nk rest =>
      simp only [multisigSigs, hs] at h
      simp only []
      cases hk : toNum false nDefaultMaxNumSize nk with
      | none => rfl
      | some nKeys =>
        simp only [hk] at h ⊢
        split <;> rename_i h1 <;> (try simp only [h1, ↓reduceIte]) <;> (try rfl)
        split <;> rename_i h2 <;> (try simp only [h2, ↓reduceIte]) <;> (try rfl)
        split <;> rename_i h3 <;> (try simp only [h3, ↓reduceIte]) <;> (try rfl)
        cases hd : rest.drop nKeys.toNat with
        | nil => simp [hd]
        | cons ns rest' =>
          simp only [hd] at h ⊢
          cases hn : toNum false nDefaultMaxNumSize ns with
          | none => simp [hn]
          | some nSigs =>
            simp only [hn] at h ⊢
            split <;> rename_i h4 <;> (try simp only [h4, ↓reduceIte]) <;> (try rfl)
            split <;> rename_i h5 <;> (try simp only [h5, ↓reduceIte]) <;> (try rfl)
            rw [multisigLoop_congr o { o with checkSig := cs } _ _ h]

/-! ### `pbegincodehash` tracking -/

theorem BitcoinScriptV2.stepV2_codesep (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s s' : BitcoinScriptV2.StateV2) (r : BitcoinScript.Bytes) (hexec : BitcoinScript.allTrue s.st.vfExec = true)
    (h : BitcoinScriptV2.stepV2 f v o s (.op BitcoinScript.OP_CODESEPARATOR, r) = some s') :
    s'.scriptCode = r := by
  simp only [stepV2, Option.map_eq_some_iff] at h
  obtain ⟨st, _, rfl⟩ := h
  simp [hexec]

theorem BitcoinScriptV2.stepV2_keeps (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s s' : BitcoinScriptV2.StateV2) (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes)
    (hno : i ≠ .op BitcoinScript.OP_CODESEPARATOR ∨ BitcoinScript.allTrue s.st.vfExec = false)
    (h : BitcoinScriptV2.stepV2 f v o s (i, r) = some s') :
    s'.scriptCode = s.scriptCode := by
  simp only [stepV2, Option.map_eq_some_iff] at h
  obtain ⟨st, _, rfl⟩ := h
  simp only
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rcases hno with hno | hno
  · exact hno h1
  · rw [hno] at h2; exact Bool.false_ne_true h2

/-- After an executed `OP_CODESEPARATOR` (the `k`-th instruction of the annotated script), the script
code is the suffix of the script's bytes following the separator byte at position `p`. -/
theorem BitcoinScriptV2.codesep_tracks (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (script : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (hl : BitcoinScriptV2.annotate script = some l) (k : Nat) (r : BitcoinScript.Bytes)
    (hk : l[k]? = some (.op BitcoinScript.OP_CODESEPARATOR, r))
    (s s' : BitcoinScriptV2.StateV2) (hexec : BitcoinScript.allTrue s.st.vfExec = true)
    (h : BitcoinScriptV2.stepV2 f v o s (.op BitcoinScript.OP_CODESEPARATOR, r) = some s') :
    s'.scriptCode = r ∧ ∃ p, script[p]? = some BitcoinScript.OP_CODESEPARATOR ∧ r = script.drop (p + 1) := by
  refine ⟨stepV2_codesep f v o s s' r hexec h, ?_⟩
  exact annotate_op_suffix script l hl _ r (List.mem_of_getElem? hk)

/-! ### The multisig script code -/

/-- The `OP_CHECKMULTISIG` loop checks against the script code with every signature deleted. -/
theorem BitcoinScriptV2.multisig_deletes_all (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (c : BitcoinScript.Byte)
    (hc : c = BitcoinScript.OP_CHECKMULTISIG ∨ c = BitcoinScript.OP_CHECKMULTISIGVERIFY) (sig pk : BitcoinScript.Bytes) :
    (BitcoinScriptV2.oracleAt v o s (.op c)).checkSig sig pk =
      o.checkSig (BitcoinScriptV2.fadAll v s.scriptCode (BitcoinScriptV2.multisigSigs s.st.stack)) sig pk := by
  rcases hc with rfl | rfl <;> rfl

theorem BitcoinScriptV2.fadAll_base (sc : BitcoinScript.Bytes) (sigs : List BitcoinScript.Bytes) :
    BitcoinScriptV2.fadAll .base sc sigs =
      sigs.foldl (fun sc sig => (BitcoinSig.findAndDelete sc (BitcoinSig.pushBytes sig)).1) sc := by
  rfl

theorem BitcoinScriptV2.fadAll_witness (sc : BitcoinScript.Bytes) (sigs : List BitcoinScript.Bytes) :
    BitcoinScriptV2.fadAll .witnessV0 sc sigs = sc := by
  induction sigs generalizing sc with
  | nil => rfl
  | cons sig sigs ih => simp only [fadAll, List.foldl_cons] at *; exact ih sc

/-- The signatures of a well-formed multisig stack `nKeys keys… nSigs sigs… rest`. -/
theorem BitcoinScriptV2.multisigSigs_eq (nk ns : BitcoinScript.Bytes) (keys sigs rest : List BitcoinScript.Bytes)
    (nKeys nSigs : Int) (hk : BitcoinScript.toNum false BitcoinScript.nDefaultMaxNumSize nk = some nKeys)
    (hkl : keys.length = nKeys.toNat) (hn : BitcoinScript.toNum false BitcoinScript.nDefaultMaxNumSize ns = some nSigs)
    (hsl : sigs.length = nSigs.toNat) :
    BitcoinScriptV2.multisigSigs (nk :: (keys ++ ns :: (sigs ++ rest))) = sigs := by
  simp only [multisigSigs, hk]
  rw [← hkl, List.drop_left]
  simp only [hn]
  rw [← hsl, List.take_left]

/-- The CHECKSIG oracle: `EvalChecksigPreTapscript` on the script code. -/
theorem BitcoinScriptV2.checksig_deletes_one (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (c : BitcoinScript.Byte)
    (hc : c = BitcoinScript.OP_CHECKSIG ∨ c = BitcoinScript.OP_CHECKSIGVERIFY) (sig pk : BitcoinScript.Bytes) :
    (BitcoinScriptV2.oracleAt v o s (.op c)).checkSig sig pk =
      o.checkSig (BitcoinScriptV2.fadSig v s.scriptCode sig) sig pk := by
  rcases hc with rfl | rfl <;> rfl

/-! ### Step agreement under the side conditions -/

private theorem foldl_id {α β : Type} (g : α → β → α) : ∀ (l : List β) (a : α), (∀ x ∈ l, g a x = a) → l.foldl g a = a
  | [], _, _ => rfl
  | x :: l, a, h => by
    simp only [List.foldl_cons, h x (by simp)]
    exact foldl_id g l a (fun y hy => h y (by simp [hy]))

/-- `step` on a skipped (non-conditional) opcode does not consult the oracle. -/
private theorem step_skipped (f : Flags) (o o' : Oracle) (s : State) (c : Byte)
    (hex : allTrue s.vfExec = false) (hc : (OP_IF ≤ c && c ≤ OP_ENDIF) = false) :
    step f o' s (.op c) = step f o s (.op c) := by
  simp only [step, hex, hc, Bool.false_or, Bool.false_eq_true, if_false]

private theorem step_multisig_congr (f : Flags) (o : Oracle) (cs : Bytes → Bytes → Option Bool) (s : State)
    (c : Byte) (hc : c = OP_CHECKMULTISIG ∨ c = OP_CHECKMULTISIGVERIFY)
    (h : ∀ sig ∈ multisigSigs s.stack, ∀ pk, cs sig pk = o.checkSig sig pk) :
    step f { o with checkSig := cs } s (.op c) = step f o s (.op c) := by
  cases hex : allTrue s.vfExec with
  | false => exact step_skipped f o _ s c hex (by rcases hc with rfl | rfl <;> decide)
  | true =>
    rcases hc with rfl | rfl <;>
    · simp (config := {decide := true}) only [step, hex, Bool.true_or, if_true, Bool.true_and, isDisabled,
        ↓reduceIte, Bool.false_or]
      split
      · rfl
      · rw [execOp_multisig_congr f o cs true _ (by first | exact Or.inl rfl | exact Or.inr rfl)
          { s with opCount := s.opCount + 1 } h]

theorem BitcoinScriptV2.stepV2_agree (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (sc : BitcoinScript.Bytes) (hsc : s.scriptCode = sc)
    (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes) (hok : BitcoinScriptV2.StepOk v s i) :
    BitcoinScriptV2.stepV2 f v o s (i, r) =
      (BitcoinScript.step f (BitcoinScriptV2.withCodeSig o v sc) s.st i).map fun st => ⟨st, sc⟩ := by
  cases i with
  | push d => simp [stepV2, oracleAt, hsc]
  | op c =>
    simp only [stepV2, oracleAt, hsc]
    cases hm : (c == OP_CHECKMULTISIG || c == OP_CHECKMULTISIGVERIFY) with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hex : allTrue s.st.vfExec with
      | false => simp
      | true =>
        have hne : c ≠ OP_CODESEPARATOR := (hok hex).1
        simp [hne]
    | true =>
      simp only [if_true]
      have hc : c = OP_CHECKMULTISIG ∨ c = OP_CHECKMULTISIGVERIFY := by
        simpa [Bool.or_eq_true, beq_iff_eq] using hm
      have hne : c ≠ OP_CODESEPARATOR := by rcases hc with rfl | rfl <;> decide
      simp only [Instr.op.injEq, hne, false_and, if_false]
      cases hex : allTrue s.st.vfExec with
      | false => rw [step_skipped f (withCodeSig o v sc) _ s.st c hex (by rcases hc with rfl | rfl <;> decide)]
      | true =>
        have hsigs := (hok hex).2 hc
        rw [hsc] at hsigs
        have hall : fadAll v sc (multisigSigs s.st.stack) = sc := foldl_id _ _ _ hsigs
        rw [hall]
        have : withCodeSig o v sc = { withCode o sc with checkSig := fun sig pk => o.checkSig (fadSig v sc sig) sig pk } := rfl
        rw [this]
        congr 1
        exact (step_multisig_congr f (withCode o sc) _ s.st c hc
          (fun sig hsig pk => by simp only [withCode, hsigs sig hsig])).symm

private theorem runV2_agree (f : Flags) (v : SigVersion) (o : OracleV2) :
    ∀ (l : List (Instr × Bytes)) (s : StateV2) (sc : Bytes), s.scriptCode = sc → RunOk f v o s l →
      runV2 f v o s l = (run f (withCodeSig o v sc) s.st (l.map Prod.fst)).map fun st => ⟨st, sc⟩
  | [], ⟨st, sc'⟩, sc, hsc, _ => by
    simp only at hsc; subst hsc
    simp only [runV2, run, List.map_nil]
    split <;> rfl
  | (i, r) :: rest, s, sc, hsc, hok => by
    obtain ⟨hstep, hrest⟩ := hok
    simp only [runV2, run, List.map_cons]
    rw [stepV2_agree f v o s sc hsc i r hstep]
    cases hst : step f (withCodeSig o v sc) s.st i with
    | none => rfl
    | some st =>
      simp only [Option.map_some]
      exact runV2_agree f v o rest ⟨st, sc⟩ sc rfl (hrest ⟨st, sc⟩ (by rw [stepV2_agree f v o s sc hsc i r hstep, hst]; rfl))

/-- Outside the two limits, the V2 interpreter is the published one with the oracle that checks against
the whole script (deleting only the checked signature). -/
theorem BitcoinScriptV2.eval_agree (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (hl : BitcoinScriptV2.annotate script = some l)
    (hok : BitcoinScriptV2.RunOk f v o ⟨BitcoinScript.State.initial stack, script⟩ l) :
    BitcoinScriptV2.evalScriptV2 f v o stack script =
      BitcoinScript.evalScript f (BitcoinScriptV2.withCodeSig o v script) stack (l.map Prod.fst) := by
  simp only [evalScriptV2, hl, evalScript]
  rw [runV2_agree f v o l ⟨State.initial stack, script⟩ script rfl hok]
  cases run f (withCodeSig o v script) (State.initial stack) (l.map Prod.fst) <;> rfl

/-- The byte-level evaluators agree outside the two limits. -/
theorem BitcoinScriptV2.evalBytes_agree (c : BitcoinVerify.Ctx) (v : BitcoinSig.SigVersion)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes) (h : BitcoinScriptV2.EvalOk c v stack script) :
    BitcoinScriptV2.evalBytesV2 c v stack script = BitcoinVerify.evalBytes c v stack script := by
  simp only [evalBytesV2, evalBytes]
  split
  · rfl
  · have hp := annotate_parse script
    cases hl : annotate script with
    | none => rw [hl] at hp; simp only [Option.map_none] at hp; rw [← hp]; simp [evalScriptV2, hl]
    | some l =>
      rw [hl] at hp; simp only [Option.map_some] at hp; rw [← hp]
      simp only
      rw [eval_agree _ v _ stack script l hl (h l hl), legacyOracle_eq]

/-! ### Static sufficient conditions -/

theorem BitcoinScriptV2.runOk_of_static (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (l : List (BitcoinScript.Instr × BitcoinScript.Bytes)) (s : BitcoinScriptV2.StateV2)
    (h1 : BitcoinScriptV2.NoCodeSep (l.map Prod.fst)) (h2 : BitcoinScriptV2.NoMultisig (l.map Prod.fst)) :
    BitcoinScriptV2.RunOk f v o s l := by
  induction l generalizing s with
  | nil => trivial
  | cons x rest ih =>
    obtain ⟨i, r⟩ := x
    simp only [NoCodeSep, NoMultisig, List.map_cons, List.mem_cons, not_or] at h1 h2
    refine ⟨?_, fun s' _ => ih s' h1.2 ⟨h2.1.2, h2.2.2⟩⟩
    cases i with
    | push _ => trivial
    | op c =>
      intro _
      refine ⟨fun hc => h1.1 (by rw [hc]), fun hc => ?_⟩
      rcases hc with hc | hc
      · exact absurd (by rw [hc]) h2.1.1
      · exact absurd (by rw [hc]) h2.2.1

theorem BitcoinScriptV2.runOk_witness (f : BitcoinScript.Flags) (o : BitcoinScriptV2.OracleV2)
    (l : List (BitcoinScript.Instr × BitcoinScript.Bytes)) (s : BitcoinScriptV2.StateV2)
    (h1 : BitcoinScriptV2.NoCodeSep (l.map Prod.fst)) :
    BitcoinScriptV2.RunOk f .witnessV0 o s l := by
  induction l generalizing s with
  | nil => trivial
  | cons x rest ih =>
    obtain ⟨i, r⟩ := x
    simp only [NoCodeSep, List.map_cons, List.mem_cons, not_or] at h1
    refine ⟨?_, fun s' _ => ih s' h1.2⟩
    cases i with
    | push _ => trivial
    | op c =>
      intro _
      exact ⟨fun hc => h1.1 (by rw [hc]), fun _ _ _ => rfl⟩

theorem BitcoinScriptV2.evalOk_of_static (c : BitcoinVerify.Ctx) (v : BitcoinSig.SigVersion)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes)
    (h : ∀ s, BitcoinSig.parseScript script = some s → BitcoinScriptV2.NoCodeSep s ∧ BitcoinScriptV2.NoMultisig s) :
    BitcoinScriptV2.EvalOk c v stack script := by
  intro l hl
  have hp := annotate_parse script
  rw [hl] at hp; simp only [Option.map_some] at hp
  obtain ⟨h1, h2⟩ := h _ hp.symm
  exact runOk_of_static _ v _ l _ h1 h2

theorem BitcoinScriptV2.evalOk_witness (c : BitcoinVerify.Ctx) (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes)
    (h : ∀ s, BitcoinSig.parseScript script = some s → BitcoinScriptV2.NoCodeSep s) :
    BitcoinScriptV2.EvalOk c .witnessV0 stack script := by
  intro l hl
  have hp := annotate_parse script
  rw [hl] at hp; simp only [Option.map_some] at hp
  exact runOk_witness _ _ l _ (h _ hp.symm)

/-! ### `VerifyScript` -/

private theorem parseScript_p2pkh (h : Bytes) (hh : h.length = 20) :
    parseScript (p2pkhBytes h) = some (p2pkhScript h) := by
  have hp : pushBytes h = (0x14 : Byte) :: h := by
    simp only [pushBytes, hh]; rfl
  simp only [parseScript, p2pkhBytes, hp, List.cons_append, List.nil_append]
  simp (config := {decide := true}) [parseScriptAux, getOp, OP_PUSHDATA4, hh, p2pkhScript]

private theorem verifyWitnessProgram_agree (tap : TaprootHandler) (c : Ctx) (witness : List Bytes) (version : Nat)
    (program : Bytes) (isP2sh : Bool)
    (h4 : ∀ script, witness.getLast? = some script → EvalOk c .witnessV0 witness.dropLast.reverse script) :
    verifyWitnessProgramV2 tap c witness version program isP2sh = verifyWitnessProgram tap c witness version program isP2sh := by
  simp only [verifyWitnessProgramV2, verifyWitnessProgram]
  split
  · split
    · cases hw : witness.getLast? with
      | none => rfl
      | some script =>
        simp only
        split
        · rfl
        · simp only [executeWitnessScriptV0V2, executeWitnessScriptV0, evalBytes_agree c .witnessV0 _ _ (h4 script hw)]
          rfl
    · split
      · split
        · rfl
        · rename_i hlen hw2
          have hok : EvalOk c .witnessV0 witness.reverse (p2wpkhExec program) := by
            apply evalOk_witness
            intro s hs
            rw [p2wpkhExec, parseScript_p2pkh program (by simpa [WITNESS_V0_KEYHASH_SIZE] using hlen)] at hs
            simp only [Option.some.injEq] at hs
            subst hs
            simp (config := {decide := true}) [NoCodeSep, p2pkhScript]
          simp only [executeWitnessScriptV0V2, executeWitnessScriptV0, evalBytes_agree c .witnessV0 _ _ hok]
          rfl
      · rfl
  · rfl

/-- `VerifyScript` agrees with the published transcription whenever every script it executes (scriptSig,
scriptPubKey, redeem script, witness script) stays outside the two limits. -/
theorem BitcoinScriptV2.verify_agree (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (scriptSig scriptPubKey : BitcoinScript.Bytes) (witness : List BitcoinScript.Bytes)
    (h1 : BitcoinScriptV2.EvalOk c .base [] scriptSig)
    (h2 : ∀ st, BitcoinScriptV2.evalBytesV2 c .base [] scriptSig = some st → BitcoinScriptV2.EvalOk c .base st scriptPubKey)
    (h3 : ∀ redeem rest, BitcoinScriptV2.evalBytesV2 c .base [] scriptSig = some (redeem :: rest) →
      BitcoinScriptV2.EvalOk c .base rest redeem)
    (h4 : ∀ script, witness.getLast? = some script → BitcoinScriptV2.EvalOk c .witnessV0 witness.dropLast.reverse script) :
    BitcoinScriptV2.verifyScriptV2 tap c scriptSig scriptPubKey witness =
      BitcoinVerify.verifyScript tap c scriptSig scriptPubKey witness := by
  simp only [verifyScriptV2, verifyScript]
  have e1 := evalBytes_agree c .base [] scriptSig h1
  rw [e1]
  cases hS : evalBytes c .base [] scriptSig with
  | none => rfl
  | some stackSig =>
    have e2 := evalBytes_agree c .base stackSig scriptPubKey (h2 stackSig (by rw [e1, hS]))
    dsimp only
    rw [e2]
    cases evalBytes c .base stackSig scriptPubKey with
    | none => rfl
    | some stack =>
      dsimp only
      simp only [verifyWitnessProgram_agree tap c witness _ _ _ h4]
      cases stackSig with
      | nil => rfl
      | cons redeem rest =>
        have e3 := evalBytes_agree c .base rest redeem (h3 redeem rest (by rw [e1, hS]))
        simp only [e3]
        rfl
