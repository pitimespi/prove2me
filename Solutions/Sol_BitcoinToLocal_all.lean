import Definitions.Def_BitcoinToLocal
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinVerify_p2wsh_correct

open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

/-! ### Script numbers -/

private theorem natBytes_length : ∀ (k n : Nat), n < 256 ^ k → (natBytes n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this; rw [natBytes]; simp
  | k + 1, n, h => by
    rw [natBytes]
    split
    · simp
    · simp only [List.length_cons]
      have := natBytes_length k (n / 256) (by rw [Nat.pow_succ] at h; omega)
      omega

/-- A script number of magnitude below `2^(8k)` serializes to at most `k + 1` bytes. -/
theorem BitcoinToLocal.serialize_length (n : Int) (k : Nat) (h : n.natAbs < 256 ^ k) :
    (BitcoinScript.serialize n).length ≤ k + 1 := by
  unfold serialize
  split
  · simp
  · have hm := natBytes_length k n.natAbs h
    dsimp only
    split
    · simp only [List.length_append, List.length_singleton]; omega
    · split
      · have : ∀ l : Bytes, (setTop l).length = l.length := by
          intro l; induction l with
          | nil => rfl
          | cons b r ih => cases r with
            | nil => rfl
            | cons c r' => simp only [setTop, List.length_cons] at ih ⊢; omega
        rw [this]; omega
      · omega

private theorem toNum_serialize5 (n : Int) (h : n.natAbs < 2 ^ 32) :
    toNum false 5 (serialize n) = some n := by
  unfold toNum
  have := BitcoinToLocal.serialize_length n 4 (by simpa using h)
  rw [if_neg (by omega)]
  simp [BitcoinScript.serialize_roundtrip]

/-! ### Single steps -/

private theorem castToBool_boolBytes (b : Bool) : castToBool (boolBytes b) = b := by
  cases b <;> rfl

/-- `step` on an executing state for an opcode above `OP_16`. -/
private theorem step_op_exec (f : Flags) (o : Oracle) (s : State) (c : BitcoinScript.Byte)
    (hc16 : OP_16 < c) (hcount : s.opCount + 1 ≤ MAX_OPS_PER_SCRIPT) (hdis : isDisabled c = false)
    (hexec : allTrue s.vfExec = true) :
    step f o s (.op c) =
      match execOp f o true c { s with opCount := s.opCount + 1 } with
      | none => none
      | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s' := by
  unfold step
  simp only [hexec, hdis, hc16, decide_true, Bool.true_and, decide_eq_true_eq, Bool.true_or,
    ite_true, Bool.false_eq_true, ite_false]
  rw [if_neg (by omega)]
  rfl

/-- `step` on a non-executing state for an opcode above `OP_16` outside `OP_IF … OP_ENDIF`. -/
private theorem step_op_skip (f : Flags) (o : Oracle) (s : State) (c : BitcoinScript.Byte)
    (hc16 : OP_16 < c) (hcount : s.opCount + 1 ≤ MAX_OPS_PER_SCRIPT) (hdis : isDisabled c = false)
    (hexec : allTrue s.vfExec = false) (hcond : ¬ (OP_IF ≤ c ∧ c ≤ OP_ENDIF)) :
    step f o s (.op c) =
      if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none
      else some { s with opCount := s.opCount + 1 } := by
  unfold step
  simp only [hexec, hdis, hc16, decide_true, Bool.true_and, decide_eq_true_eq, Bool.false_or,
    ite_true, Bool.false_eq_true, ite_false]
  rw [if_neg (show ¬ MAX_OPS_PER_SCRIPT < s.opCount + 1 by simp only [MAX_OPS_PER_SCRIPT] at hcount ⊢; omega)]
  have : (decide (OP_IF ≤ c) && decide (c ≤ OP_ENDIF)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hA : OP_IF ≤ c
    · exact Or.inr (fun hB => hcond ⟨hA, hB⟩)
    · exact Or.inl hA
  rw [this]
  simp

/-- `step` on a conditional opcode (`OP_IF`, `OP_ELSE`, `OP_ENDIF`), executing or not. -/
private theorem step_op_cond (f : Flags) (o : Oracle) (s : State) (c : BitcoinScript.Byte)
    (hc16 : OP_16 < c) (hcount : s.opCount + 1 ≤ MAX_OPS_PER_SCRIPT) (hdis : isDisabled c = false)
    (hcond : OP_IF ≤ c ∧ c ≤ OP_ENDIF) :
    step f o s (.op c) =
      match execOp f o (allTrue s.vfExec) c { s with opCount := s.opCount + 1 } with
      | none => none
      | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s' := by
  unfold step
  have : (OP_IF ≤ c && c ≤ OP_ENDIF) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hcond
  simp only [hdis, hc16, this, decide_true, Bool.true_and, decide_eq_true_eq, Bool.or_true,
    ite_true, Bool.false_eq_true, ite_false]
  rw [if_neg (by omega)]
  rfl

private theorem step_push_exec (f : Flags) (o : Oracle) (s : State) (d : Bytes)
    (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue s.vfExec = true) :
    step f o s (.push d) =
      if MAX_STACK_SIZE < s.stack.length + 1 + s.altstack.length then none
      else some { s with stack := d :: s.stack } := by
  dsimp only [step]
  rw [if_neg (show ¬ MAX_SCRIPT_ELEMENT_SIZE < d.length by omega)]
  simp [hexec]

private theorem step_push_skip (f : Flags) (o : Oracle) (s : State) (d : Bytes)
    (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue s.vfExec = false) :
    step f o s (.push d) =
      if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none else some s := by
  dsimp only [step]
  rw [if_neg (show ¬ MAX_SCRIPT_ELEMENT_SIZE < d.length by omega)]
  simp [hexec]

private theorem execOp_if_exec (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_IF s = match s.stack with
      | [] => none
      | top :: rest => some { s with stack := rest, vfExec := castToBool top :: s.vfExec } := by
  rfl

private theorem execOp_else (f : Flags) (o : Oracle) (e : Bool) (s : State) :
    execOp f o e OP_ELSE s = match s.vfExec with
      | [] => none
      | b :: rest => some { s with vfExec := (!b) :: rest } := by
  cases e <;> rfl

private theorem execOp_endif (f : Flags) (o : Oracle) (e : Bool) (s : State) :
    execOp f o e OP_ENDIF s = match s.vfExec with
      | [] => none
      | _ :: rest => some { s with vfExec := rest } := by
  cases e <;> rfl

private theorem execOp_drop (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_DROP s = match s.stack with
      | [] => none
      | _ :: rest => some { s with stack := rest } := by
  rfl

private theorem execOp_checksig (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKSIG s = match s.stack with
      | pubkey :: sig :: rest =>
        match o.checkSig sig pubkey with
        | none => none
        | some ok => some { s with stack := boolBytes ok :: rest }
      | _ => none := by
  rfl

private theorem execOp_csv (f : Flags) (o : Oracle) (s : State) :
    execOp f o true OP_CHECKSEQUENCEVERIFY s =
      if !f.csv then some s
      else match s.stack with
        | [] => none
        | top :: _ =>
          match toNum false 5 top with
          | none => none
          | some n =>
            if n < 0 then none
            else if (n.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG) != 0 then some s
            else if !o.checkSequence n then none else some s := by
  rfl

/-- `OP_CHECKSEQUENCEVERIFY` on a stack whose top is the serialization of a 5-byte number. -/
theorem BitcoinToLocal.csv_step (f : Flags) (o : Oracle) (s : State) (delay : Int) (rest : List Bytes)
    (hs : s.stack = BitcoinScript.serialize delay :: rest) (hd : delay.natAbs < 2 ^ 32) :
    BitcoinScript.execOp f o true BitcoinScript.OP_CHECKSEQUENCEVERIFY s =
      if BitcoinToLocal.CsvPasses f o delay then some s else none := by
  rw [execOp_csv, hs]
  dsimp only
  rw [toNum_serialize5 delay hd]
  dsimp only
  by_cases hc : f.csv = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases h0 : delay < 0
    · rw [if_pos h0, if_neg]
      unfold CsvPasses; simp only [hc, Bool.true_eq_false, false_or, not_and]; intro; omega
    · rw [if_neg h0]
      by_cases hdis : (delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0
      · have h' : (delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG != 0) = true := by simpa using hdis
        rw [if_pos h', if_pos]
        unfold CsvPasses; exact Or.inr ⟨by omega, Or.inl hdis⟩
      · have h' : (delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG != 0) = false := by simpa using hdis
        rw [if_neg (by simp [h'])]
        by_cases hcs : o.checkSequence delay = true
        · simp only [hcs, Bool.not_true, Bool.false_eq_true, ite_false]
          rw [if_pos]
          unfold CsvPasses; exact Or.inr ⟨by omega, Or.inr hcs⟩
        · simp only [Bool.not_eq_true] at hcs
          simp only [hcs, Bool.not_false, ite_true]
          rw [if_neg]
          unfold CsvPasses
          simp only [hc, Bool.true_eq_false, false_or, hcs, Bool.false_eq_true, or_false, not_and]
          intro; exact hdis
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.not_false, ite_true]
    rw [if_pos]
    unfold CsvPasses; exact Or.inl hc
/-! ### Small-number instructions -/

private theorem step_op_n (f : Flags) (o : Oracle) (s : State) (c : BitcoinScript.Byte)
    (hc16 : c ≤ OP_16) (hdis : isDisabled c = false) (hcond : ¬ OP_IF ≤ c) :
    step f o s (.op c) =
      if allTrue s.vfExec then
        match execOp f o true c s with
        | none => none
        | some s' => if MAX_STACK_SIZE < s'.stack.length + s'.altstack.length then none else some s'
      else if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none else some s := by
  unfold step
  have h1 : decide (OP_16 < c) = false := by simp only [decide_eq_false_iff_not]; exact fun h => absurd hc16 (BitVec.not_le.mpr h)
  have h2 : decide (OP_IF ≤ c) = false := by simp only [decide_eq_false_iff_not]; exact hcond
  simp only [h1, h2, hdis, Bool.false_and, Bool.false_eq_true, ite_false, Bool.or_false]
  cases allTrue s.vfExec
  · simp
  · simp only [ite_true]
    rfl

private def opByte (n : Int) : BitcoinScript.Byte := BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat

private theorem opn_facts (n : Int) (hn : n = -1 ∨ (1 ≤ n ∧ n ≤ 16)) :
    opByte n ≤ OP_16 ∧ isDisabled (opByte n) = false ∧ ¬ OP_IF ≤ opByte n ∧
      (opByte n == OP_1NEGATE || (OP_1 ≤ opByte n && opByte n ≤ OP_16)) = true ∧
      ((opByte n).toNat : Int) - ((OP_1.toNat : Int) - 1) = n := by
  have h : n = -1 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem numInstr_exec (f : Flags) (o : Oracle) (s : State) (n : Int)
    (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue s.vfExec = true) :
    step f o s (numInstr n) =
      if MAX_STACK_SIZE < s.stack.length + 1 + s.altstack.length then none
      else some { s with stack := serialize n :: s.stack } := by
  unfold numInstr
  split
  · rename_i h
    obtain ⟨h1, h2, h3, h4, h5⟩ := opn_facts n h
    rw [show (BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat) = opByte n from rfl]
    rw [step_op_n f o s _ h1 h2 h3, if_pos hexec]
    unfold execOp
    rw [if_pos h4]
    simp only [pushNum, h5, List.length_cons]
  · exact step_push_exec f o s _ hn hexec

private theorem numInstr_skip (f : Flags) (o : Oracle) (s : State) (n : Int)
    (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hexec : allTrue s.vfExec = false) :
    step f o s (numInstr n) =
      if MAX_STACK_SIZE < s.stack.length + s.altstack.length then none else some s := by
  unfold numInstr
  split
  · rename_i h
    obtain ⟨h1, h2, h3, -, -⟩ := opn_facts n h
    rw [show (BitVec.ofNat 8 (n + (OP_1.toNat - 1)).toNat) = opByte n from rfl]
    rw [step_op_n f o s _ h1 h2 h3, if_neg (by simp [hexec])]
  · exact step_push_skip f o s _ hn hexec

/-! ### Bit lemmas -/

private theorem and_two_pow_eq_zero (n k : Nat) (h : n < 2 ^ k) : n &&& 2 ^ k = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : k = i
  · subst hi; rw [Nat.testBit_lt_two_pow h]; rfl
  · simp [hi]

example (n : Nat) (h : n < 2 ^ 16) : n &&& (2 ^ 22 ||| 0xffff) = n := by
  rw [Nat.and_or_distrib_left, and_two_pow_eq_zero n 22 (by omega), Nat.zero_or]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 16) h

/-! ### Running the script -/

private theorem allTrue_nil : allTrue [] = true := rfl
private theorem allTrue_true : allTrue [true] = true := rfl
private theorem allTrue_false : allTrue [false] = false := rfl

set_option maxHeartbeats 1000000 in
private theorem run_cons (f : Flags) (o : Oracle) (rev dpk b : Bytes) (delay : Int) (tl : List Bytes)
    (hrev : rev.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) (htl : tl.length + 1 ≤ MAX_STACK_SIZE) :
    evalScript f o (b :: tl) (toLocalScript rev delay dpk) =
      match tl with
      | [] => none
      | sig :: rest =>
        if castToBool b then (o.checkSig sig rev).map (fun ok => boolBytes ok :: rest)
        else if CsvPasses f o delay then (o.checkSig sig dpk).map (fun ok => boolBytes ok :: rest) else none := by
  have hser : (serialize delay).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
    Nat.le_trans (BitcoinToLocal.serialize_length delay 4 (by simpa using hd)) (by decide)
  simp only [MAX_STACK_SIZE] at htl
  unfold evalScript toLocalScript State.initial
  -- OP_IF
  rw [run, step_op_cond f o _ OP_IF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
  rw [allTrue_nil, execOp_if_exec]
  dsimp only
  rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
  dsimp only
  by_cases hb : castToBool b = true
  · rw [hb]
    -- push rev (executing)
    rw [run, step_push_exec f o _ rev hrev allTrue_true]
    rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_ELSE
    rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
    rw [execOp_else]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- the number (skipped)
    rw [run, numInstr_skip f o _ delay hser allTrue_false]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKSEQUENCEVERIFY (skipped)
    rw [run, step_op_skip f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_false (by decide)]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_DROP (skipped)
    rw [run, step_op_skip f o _ OP_DROP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_false (by decide)]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- push dpk (skipped)
    rw [run, step_push_skip f o _ dpk hdpk allTrue_false]
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_ENDIF
    rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
    rw [execOp_endif]
    dsimp only
    rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKSIG
    rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
    rw [execOp_checksig]
    cases tl with
    | nil => rfl
    | cons sig rest =>
      dsimp only
      cases o.checkSig sig rev with
      | none => rfl
      | some ok =>
        dsimp only
        simp only [List.length_cons, List.length_nil] at htl ⊢
        rw [if_neg (by simp only [MAX_STACK_SIZE]; omega)]
        dsimp only
        simp [run]
  · simp only [Bool.not_eq_true] at hb
    rw [hb]
    -- push rev (skipped)
    rw [run, step_push_skip f o _ rev hrev allTrue_false]
    rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_ELSE
    rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
    rw [execOp_else]
    dsimp only
    rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- the number (executing)
    rw [run, numInstr_exec f o _ delay hser allTrue_true]
    rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    -- OP_CHECKSEQUENCEVERIFY
    rw [run, step_op_exec f o _ OP_CHECKSEQUENCEVERIFY (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_true]
    rw [BitcoinToLocal.csv_step f o _ delay tl rfl hd]
    by_cases hcsv : CsvPasses f o delay
    · rw [if_pos hcsv]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_DROP
      rw [run, step_op_exec f o _ OP_DROP (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_true]
      rw [execOp_drop]
      dsimp only
      rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- push dpk
      rw [run, step_push_exec f o _ dpk hdpk allTrue_true]
      rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_ENDIF
      rw [run, step_op_cond f o _ OP_ENDIF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
      rw [execOp_endif]
      dsimp only
      rw [if_neg (by simp only [List.length_cons, List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      -- OP_CHECKSIG
      rw [run, step_op_exec f o _ OP_CHECKSIG (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) allTrue_nil]
      rw [execOp_checksig]
      cases tl with
      | nil => rfl
      | cons sig rest =>
        dsimp only
        cases o.checkSig sig dpk with
        | none => simp [hcsv]
        | some ok =>
          dsimp only
          simp only [List.length_cons, List.length_nil] at htl ⊢
          rw [if_neg (by simp only [MAX_STACK_SIZE]; omega)]
          dsimp only
          simp [run, hcsv]
    · rw [if_neg hcsv]
      cases tl with
      | nil => rfl
      | cons sig rest => simp [hcsv]

/-- The script on a stack `b :: tl` (top first) of admissible size: it fails unless `tl` is a single
signature, otherwise it leaves the result of the chosen signature check above whatever lies below. -/
theorem BitcoinToLocal.eval_cons (f : Flags) (o : Oracle) (rev dpk b : Bytes) (delay : Int) (tl : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) (htl : tl.length + 1 ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (b :: tl) (BitcoinToLocal.toLocalScript rev delay dpk) =
      match tl with
      | [] => none
      | sig :: rest =>
        if BitcoinScript.castToBool b then (o.checkSig sig rev).map (fun ok => BitcoinScript.boolBytes ok :: rest)
        else if BitcoinToLocal.CsvPasses f o delay then (o.checkSig sig dpk).map (fun ok => BitcoinScript.boolBytes ok :: rest)
        else none :=
  run_cons f o rev dpk b delay tl hrev hdpk hd htl

private theorem eval_nil (f : Flags) (o : Oracle) (rev dpk : Bytes) (delay : Int) :
    evalScript f o [] (toLocalScript rev delay dpk) = none := by
  unfold evalScript toLocalScript State.initial
  rw [run, step_op_cond f o _ OP_IF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
  rw [allTrue_nil, execOp_if_exec]
  rfl

private theorem eval_large (f : Flags) (o : Oracle) (rev dpk b : Bytes) (delay : Int) (tl : List Bytes)
    (hrev : rev.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hd : delay.natAbs < 2 ^ 32)
    (htl : MAX_STACK_SIZE < tl.length + 1) :
    evalScript f o (b :: tl) (toLocalScript rev delay dpk) = none := by
  have hser : (serialize delay).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
    Nat.le_trans (BitcoinToLocal.serialize_length delay 4 (by simpa using hd)) (by decide)
  simp only [MAX_STACK_SIZE] at htl
  unfold evalScript toLocalScript State.initial
  rw [run, step_op_cond f o _ OP_IF (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
  rw [allTrue_nil, execOp_if_exec]
  dsimp only
  by_cases hbig : 1000 < tl.length
  · rw [if_pos (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    rfl
  · rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
    dsimp only
    by_cases hb : castToBool b = true
    · rw [hb, run, step_push_exec f o _ rev hrev allTrue_true]
      rw [if_pos (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
      rfl
    · simp only [Bool.not_eq_true] at hb
      rw [hb, run, step_push_skip f o _ rev hrev allTrue_false]
      rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run, step_op_cond f o _ OP_ELSE (by decide) (by simp [MAX_OPS_PER_SCRIPT]) (by decide) (by decide)]
      rw [execOp_else]
      dsimp only
      rw [if_neg (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
      dsimp only
      rw [run, numInstr_exec f o _ delay hser allTrue_true]
      rw [if_pos (by simp only [List.length_nil, MAX_STACK_SIZE]; omega)]
      rfl

/-- **The two spending conditions.** A witness stack satisfies the `to_local` script under the
witness-v0 rule (exactly one element left, and it true) exactly when it consists of a signature
and a branch selector, and the selected branch's conditions hold. -/
theorem BitcoinToLocal.spends_iff (f : Flags) (o : Oracle) (rev dpk : Bytes) (delay : Int) (st : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinToLocal.toLocalScript rev delay dpk) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      ∃ b sig, st = [b, sig] ∧ BitcoinToLocal.SpendCondition f o rev delay dpk b sig := by
  constructor
  · rintro ⟨res, hres, hlen, htop⟩
    cases st with
    | nil => rw [eval_nil] at hres; cases hres
    | cons b tl =>
      by_cases htl : tl.length + 1 ≤ MAX_STACK_SIZE
      · rw [BitcoinToLocal.eval_cons f o rev dpk b delay tl hrev hdpk hd htl] at hres
        cases tl with
        | nil => cases hres
        | cons sig rest =>
          refine ⟨b, sig, ?_, ?_⟩
          · -- the stack below the signature must be empty
            dsimp only at hres
            split at hres
            · cases hcs : o.checkSig sig rev with
              | none => rw [hcs] at hres; cases hres
              | some ok =>
                rw [hcs] at hres; simp only [Option.map_some, Option.some.injEq] at hres
                subst hres; simp only [List.length_cons] at hlen
                have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
                subst this; rfl
            · split at hres
              · cases hcs : o.checkSig sig dpk with
                | none => rw [hcs] at hres; cases hres
                | some ok =>
                  rw [hcs] at hres; simp only [Option.map_some, Option.some.injEq] at hres
                  subst hres; simp only [List.length_cons] at hlen
                  have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
                  subst this; rfl
              · cases hres
          · dsimp only at hres
            unfold SpendCondition
            split at hres
            · rename_i hb
              left; refine ⟨hb, ?_⟩
              cases hcs : o.checkSig sig rev with
              | none => rw [hcs] at hres; cases hres
              | some ok =>
                rw [hcs] at hres; simp only [Option.map_some, Option.some.injEq] at hres
                subst hres; simp only [topTrue, castToBool_boolBytes] at htop; rw [htop]
            · rename_i hb
              split at hres
              · rename_i hcsv
                right; refine ⟨by simpa using hb, hcsv, ?_⟩
                cases hcs : o.checkSig sig dpk with
                | none => rw [hcs] at hres; cases hres
                | some ok =>
                  rw [hcs] at hres; simp only [Option.map_some, Option.some.injEq] at hres
                  subst hres; simp only [topTrue, castToBool_boolBytes] at htop; rw [htop]
              · cases hres
      · rw [eval_large f o rev dpk b delay tl hrev hd (by omega)] at hres; cases hres
  · rintro ⟨b, sig, rfl, hsc⟩
    rw [BitcoinToLocal.eval_cons f o rev dpk b delay [sig] hrev hdpk hd (by simp [MAX_STACK_SIZE])]
    dsimp only
    unfold SpendCondition at hsc
    rcases hsc with ⟨hb, hcs⟩ | ⟨hb, hcsv, hcs⟩
    · rw [if_pos hb, hcs]; exact ⟨_, rfl, rfl, rfl⟩
    · rw [if_neg (by simp [hb]), if_pos hcsv, hcs]; exact ⟨_, rfl, rfl, rfl⟩

/-! ### Parsing the byte form -/

private theorem getOp_op (c : BitcoinScript.Byte) (rest : Bytes) (hc : OP_PUSHDATA4 < c.toNat) :
    getOp (c :: rest) = some (.op c, rest) := by
  unfold getOp
  dsimp only
  rw [if_neg (Nat.not_le.mpr hc)]

private theorem pushBytes_short (d : Bytes) (hd : d.length < 76) : pushBytes d = BitVec.ofNat 8 d.length :: d := by
  unfold pushBytes OP_PUSHDATA1; rw [if_pos hd]

private theorem leBytes_len (k n : Nat) : (BitcoinSer.leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [BitcoinSer.leBytes, ih]

private theorem leVal_leBytes2 (n : Nat) (h : n < 65536) : BitcoinSer.leVal (BitcoinSer.leBytes 2 n) = n := by
  simp [BitcoinSer.leBytes, BitcoinSer.leVal, BitVec.toNat_ofNat]; omega

private theorem getOp_pushBytes (d rest : Bytes) (hd : d.length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    getOp (pushBytes d ++ rest) = some (.push d, rest) := by
  unfold MAX_SCRIPT_ELEMENT_SIZE at hd
  have hlen : ¬ (d.length + rest.length < d.length) := by omega
  unfold pushBytes OP_PUSHDATA1 OP_PUSHDATA2 OP_PUSHDATA4
  by_cases h1 : d.length < 76
  · rw [if_pos h1]
    simp only [List.cons_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4, BitVec.toNat_ofNat, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp [h1, hlen]
    omega
  · rw [if_neg h1]
    by_cases h2 : d.length ≤ 0xff
    · rw [if_pos h2]
      simp only [List.cons_append, List.nil_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp [hlen]
    · rw [if_neg h2, if_pos (by omega)]
      have hl : (BitcoinSer.leBytes 2 d.length ++ (d ++ rest)).length = 2 + (d.length + rest.length) := by
        simp [leBytes_len]
      simp only [List.cons_append, getOp, OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, List.append_assoc]
      simp only [show (77:Nat) ≤ 78 from by omega, show ¬ ((77:Nat) < 76) from by omega, show (77:Nat) ≠ 76 from by omega,
        if_true, if_false, ite_true, ite_false, ne_eq, not_false_eq_true, not_true_eq_false]
      rw [if_neg (by rw [hl]; omega),
        List.take_left' (leBytes_len 2 _), List.drop_left' (leBytes_len 2 _), leVal_leBytes2 _ (by omega)]
      simp [hlen]

private theorem pushBytes_length_le (d : Bytes) : (pushBytes d).length ≤ d.length + 5 := by
  unfold pushBytes
  split
  · simp
  · split
    · simp
    · split
      · simp [leBytes_len]; omega
      · simp [leBytes_len]; omega

private theorem pushBytes_length_pos (d : Bytes) : 1 ≤ (pushBytes d).length := by
  unfold pushBytes
  split
  · simp
  · split
    · simp
    · split
      · simp
      · simp

private theorem parseScriptAux_step (fuel : Nat) (s r : Bytes) (i : Instr) (h : getOp s = some (i, r)) :
    parseScriptAux (fuel + 1) s = (parseScriptAux fuel r).map (i :: ·) := by
  cases s with
  | nil => simp [getOp] at h
  | cons b bs =>
    simp only [parseScriptAux, h]
    cases parseScriptAux fuel r <;> rfl

private theorem parseScriptAux_nil (fuel : Nat) : parseScriptAux fuel [] = some [] := by
  cases fuel <;> rfl

private theorem getOp_numBytes (n : Int) (rest : Bytes) (hn : (serialize n).length ≤ MAX_SCRIPT_ELEMENT_SIZE) :
    getOp (numBytes n ++ rest) = some (numInstr n, rest) := by
  unfold numBytes numInstr
  split
  · rename_i h
    simp only [List.cons_append, List.nil_append]
    apply getOp_op
    have h17 : n = -1 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨
        n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by omega
    rcases h17 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact getOp_pushBytes _ _ hn

private theorem numBytes_length_le (n : Int) : (numBytes n).length ≤ (serialize n).length + 5 := by
  unfold numBytes
  split
  · simp
  · exact pushBytes_length_le _

/-- `CScript`'s byte form of the script parses to its instruction form. -/
theorem BitcoinToLocal.parseScript_toLocal (rev dpk : Bytes) (delay : Int)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    BitcoinSig.parseScript (BitcoinToLocal.toLocalBytes rev delay dpk) = some (BitcoinToLocal.toLocalScript rev delay dpk) := by
  have hser : (serialize delay).length ≤ MAX_SCRIPT_ELEMENT_SIZE :=
    Nat.le_trans (BitcoinToLocal.serialize_length delay 4 (by simpa using hd)) (by decide)
  unfold parseScript
  have hlen : ∃ m, (toLocalBytes rev delay dpk).length = m + 9 := by
    refine ⟨(toLocalBytes rev delay dpk).length - 9, ?_⟩
    have h1 := pushBytes_length_pos rev
    have h2 := pushBytes_length_pos dpk
    have h3 : 1 ≤ (numBytes delay).length := by
      unfold numBytes; split
      · simp
      · exact pushBytes_length_pos _
    simp only [toLocalBytes, List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨m, hm⟩ := hlen
  rw [hm]
  unfold toLocalBytes toLocalScript
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [parseScriptAux_step _ _ _ _ (getOp_op OP_IF _ (by decide))]
  rw [parseScriptAux_step _ _ _ _ (getOp_pushBytes rev _ hrev)]
  rw [parseScriptAux_step _ _ _ _ (getOp_op OP_ELSE _ (by decide))]
  rw [parseScriptAux_step _ _ _ _ (getOp_numBytes delay _ hser)]
  rw [parseScriptAux_step _ _ _ _ (getOp_op OP_CHECKSEQUENCEVERIFY _ (by decide))]
  rw [parseScriptAux_step _ _ _ _ (getOp_op OP_DROP _ (by decide))]
  rw [parseScriptAux_step _ _ _ _ (getOp_pushBytes dpk _ hdpk)]
  rw [parseScriptAux_step _ _ _ _ (getOp_op OP_ENDIF _ (by decide))]
  rw [parseScriptAux_step _ _ _ _ (getOp_op OP_CHECKSIG _ (by decide))]
  rw [parseScriptAux_nil]
  rfl

/-! ### The output under `VerifyScript` -/

private theorem toLocalBytes_length (rev dpk : Bytes) (delay : Int)
    (hrev : rev.length ≤ MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) : (toLocalBytes rev delay dpk).length ≤ MAX_SCRIPT_SIZE := by
  have h1 := pushBytes_length_le rev
  have h2 := pushBytes_length_le dpk
  have h3 := numBytes_length_le delay
  have h4 := BitcoinToLocal.serialize_length delay 4 (by simpa using hd)
  simp only [toLocalBytes, List.length_append, List.length_cons, List.length_nil, MAX_SCRIPT_SIZE,
    MAX_SCRIPT_ELEMENT_SIZE] at *
  omega

/-- **The `to_local` output.** Paid to as pay-to-witness-script-hash, the output is spent by a witness
exactly when the witness is a signature, a branch selector and the script, and the selected branch's
conditions hold for the transaction's own signature checker and sequence check (the first conjunct
is `VerifyScript`'s requirement that the program itself be a true value). -/
theorem BitcoinToLocal.p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (rev dpk : Bytes) (delay : Int) (ws : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinToLocal.toLocalBytes rev delay dpk)))
        (ws ++ [BitcoinToLocal.toLocalBytes rev delay dpk]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinToLocal.toLocalBytes rev delay dpk)) = true ∧
      ∃ b sig, ws = [sig, b] ∧ sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE ∧ b.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE ∧
        BitcoinToLocal.SpendCondition (BitcoinVerify.scriptFlagsOf c.flags)
          (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 (BitcoinToLocal.toLocalBytes rev delay dpk))
          rev delay dpk b sig := by
  rw [BitcoinVerify.p2wsh_correct tap c ws _ hf]
  apply and_congr_right
  intro _
  unfold executeWitnessScriptV0 evalBytes
  rw [if_neg (Nat.not_lt.mpr (toLocalBytes_length rev dpk delay hrev hdpk hd)),
    BitcoinToLocal.parseScript_toLocal rev dpk delay hrev hdpk hd]
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hany
      dsimp only at h
      cases hev : evalScript (scriptFlagsOf c.flags)
          (legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 (toLocalBytes rev delay dpk))
          ws.reverse (toLocalScript rev delay dpk) with
      | none => rw [hev] at h; cases h
      | some res =>
        rw [hev] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨b, sig, hws, hsc⟩ := (BitcoinToLocal.spends_iff _ _ rev dpk delay ws.reverse hrev hdpk hd).1 ⟨res, hev, h.1, h.2⟩
        have hws' : ws = [sig, b] := by
          rw [← List.reverse_reverse ws, hws]; rfl
        subst hws'
        have h1 : ¬ (MAX_SCRIPT_ELEMENT_SIZE < b.length) := by
          intro hlt; simp [hlt] at hany
        have h2 : ¬ (MAX_SCRIPT_ELEMENT_SIZE < sig.length) := by
          intro hlt; simp [hlt] at hany
        exact ⟨b, sig, rfl, Nat.not_lt.mp h2, Nat.not_lt.mp h1, hsc⟩
  · rintro ⟨b, sig, rfl, hsig, hb, hsc⟩
    rw [if_neg (by simp [hb, hsig])]
    obtain ⟨res, hev, hl, ht⟩ := (BitcoinToLocal.spends_iff _ _ rev dpk delay [b, sig] hrev hdpk hd).2 ⟨b, sig, rfl, hsc⟩
    have : ([sig, b] : List Bytes).reverse = [b, sig] := rfl
    rw [this]
    dsimp only
    rw [hev]
    simp [hl, ht]

/-! ### The delay in terms of the spending transaction -/

private theorem small_and_mask (n : Nat) (h : n < 2 ^ 16) :
    n &&& (BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ||| BitcoinSig.SEQUENCE_LOCKTIME_MASK) = n := by
  unfold BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG BitcoinSig.SEQUENCE_LOCKTIME_MASK
  rw [Nat.and_or_distrib_left, and_two_pow_eq_zero n 22 (by omega), Nat.zero_or]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 16) h

/-- With the `CHECKSEQUENCEVERIFY` flag on and a delay below `2^16` (BOLT #3's `to_self_delay` is a
16-bit value), the operand check reduces to the transaction's `CheckSequence`. -/
theorem BitcoinToLocal.csv_concrete (f : Flags) (sf : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : Bytes) (delay : Int) (hcsv : f.csv = true) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16) :
    BitcoinToLocal.CsvPasses f (BitcoinSig.legacyOracle sf tx nIn amount v sc) delay ↔
      BitcoinSig.checkSequence tx nIn delay = true := by
  unfold CsvPasses
  have hdis : delay.toNat &&& BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 := by
    unfold BitcoinScript.SEQUENCE_LOCKTIME_DISABLE_FLAG
    exact and_two_pow_eq_zero _ 31 (by omega)
  simp only [hcsv, Bool.true_eq_false, false_or, hdis, ne_eq, not_true_eq_false, false_or, legacyOracle]
  exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩

/-- `CheckSequence` for a delay below `2^16`: the transaction is version 2 or later, the input's
`nSequence` has neither the disable flag nor the time-type flag, and its low 16 bits are at least
the delay. -/
theorem BitcoinToLocal.checkSequence_iff (tx : BitcoinSer.Tx) (nIn : Nat) (delay : Int) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16) :
    BitcoinSig.checkSequence tx nIn delay = true ↔
      2 ≤ tx.version ∧
      BitcoinToLocal.inputSequence tx nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      BitcoinToLocal.inputSequence tx nIn &&& (BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ||| BitcoinSig.SEQUENCE_LOCKTIME_MASK) <
        BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ∧
      delay.toNat ≤ BitcoinToLocal.inputSequence tx nIn &&& (BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ||| BitcoinSig.SEQUENCE_LOCKTIME_MASK) := by
  unfold BitcoinSig.checkSequence
  rw [show (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence = inputSequence tx nIn from rfl]
  dsimp only
  rw [small_and_mask delay.toNat (by omega)]
  generalize inputSequence tx nIn &&& (BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ||| BitcoinSig.SEQUENCE_LOCKTIME_MASK) = m
  have hT : BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG = 2 ^ 22 := rfl
  rw [hT] at *
  by_cases hv : tx.version < 2
  · rw [if_pos hv]; simp; omega
  · rw [if_neg hv]
    by_cases hdis : inputSequence tx nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG ≠ 0
    · rw [if_pos hdis]
      constructor
      · intro h; cases h
      · rintro ⟨-, h, -⟩; exact absurd h hdis
    · rw [if_neg hdis]
      have hdis : inputSequence tx nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 := Decidable.of_not_not hdis
      by_cases hm : m < 2 ^ 22
      · rw [if_neg (by omega)]
        by_cases hlt : m < delay.toNat
        · rw [if_pos hlt]; simp; omega
        · rw [if_neg hlt]; simp; omega
      · rw [if_pos (by omega)]; simp; omega

/-- A Lightning commitment spend sets `nSequence` to the delay itself (no flags, below `2^16`):
then the delayed path is open exactly when the transaction is version 2 or later and `nSequence`
is at least `to_self_delay`. -/
theorem BitcoinToLocal.lightning_delay (tx : BitcoinSer.Tx) (nIn : Nat) (delay : Int) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16)
    (hseq : BitcoinToLocal.inputSequence tx nIn < 2 ^ 16) :
    BitcoinSig.checkSequence tx nIn delay = true ↔ 2 ≤ tx.version ∧ delay.toNat ≤ BitcoinToLocal.inputSequence tx nIn := by
  rw [BitcoinToLocal.checkSequence_iff tx nIn delay h0 h16, small_and_mask _ hseq]
  have hdis : inputSequence tx nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 := by
    unfold BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG
    exact and_two_pow_eq_zero _ 31 (by omega)
  have hT : inputSequence tx nIn < BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG := by
    unfold BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG; omega
  simp only [hdis, hT, true_and]
