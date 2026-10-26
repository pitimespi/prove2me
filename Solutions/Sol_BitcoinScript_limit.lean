import Definitions.Def_BitcoinScript
import Solutions.Sol_BitcoinScript_opcount

open BitcoinScript

private theorem step_push_opCount (f : Flags) (o : Oracle) (s s' : State) (d : Bytes)
    (h : step f o s (.push d) = some s') : s'.opCount = s.opCount := by
  unfold step at h
  dsimp only at h
  repeat' split at h
  all_goals (cases h; try rfl)

private theorem step_op_opCount (f : Flags) (o : Oracle) (s s' : State) (c : Byte)
    (h : step f o s (.op c) = some s') :
    s.opCount + 1 ≤ s'.opCount ∧ s'.opCount ≤ MAX_OPS_PER_SCRIPT := by
  unfold step at h
  dsimp only at h
  by_cases h1 : MAX_OPS_PER_SCRIPT < s.opCount + 1
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : isDisabled c = true
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      split at h
      · split at h
        · cases h
        · rename_i hcond x sx hex
          split at h
          · cases h
          · have hoc := BitcoinScript.execOp_opCount f o _ c _ sx hex
            simp only at hoc
            cases h
            constructor <;> omega
      · cases h
        constructor <;> simp <;> omega

private theorem run_opCount (f : Flags) (o : Oracle) :
    ∀ (script : Script) (s s' : State), run f o s script = some s' →
      s.opCount + BitcoinScript.opsIn script ≤ s'.opCount ∧
      (0 < BitcoinScript.opsIn script → s'.opCount ≤ MAX_OPS_PER_SCRIPT)
  | [], s, s', h => by
    unfold run at h
    split at h
    · cases h; simp [BitcoinScript.opsIn]
    · cases h
  | i :: rest, s, s', h => by
    unfold run at h
    cases hstep : step f o s i with
    | none => rw [hstep] at h; cases h
    | some s1 =>
      rw [hstep] at h
      have ih := run_opCount f o rest s1 s' h
      cases i with
      | push d =>
        have e := step_push_opCount f o s s1 d hstep
        simp only [BitcoinScript.opsIn] at *
        constructor
        · omega
        · intro hpos; exact ih.2 hpos
      | op c =>
        have hs := step_op_opCount f o s s1 c hstep
        simp only [BitcoinScript.opsIn] at *
        refine ⟨by omega, fun _ => ?_⟩
        by_cases hr : 0 < BitcoinScript.opsIn rest
        · exact ih.2 hr
        · -- the tail is push-only, so the count is unchanged from s1
          have h0 : BitcoinScript.opsIn rest = 0 := by omega
          suffices hp : ∀ (t : Script) (a b : State), BitcoinScript.opsIn t = 0 → run f o a t = some b → b.opCount = a.opCount by
            rw [hp rest s1 s' h0 h]; exact hs.2
          intro t
          induction t with
          | nil =>
            intro a b _ hr
            unfold run at hr
            split at hr
            · cases hr; rfl
            · cases hr
          | cons j tl iht =>
            intro a b h0' hr
            cases j with
            | op _ => simp [BitcoinScript.opsIn] at h0'
            | push d =>
              simp only [BitcoinScript.opsIn] at h0'
              unfold run at hr
              cases hst : step f o a (.push d) with
              | none => rw [hst] at hr; cases hr
              | some a1 =>
                rw [hst] at hr
                rw [iht a1 b h0' hr, step_push_opCount f o a a1 d hst]

/-- A script with more than `MAX_OPS_PER_SCRIPT` non-push instructions never evaluates
successfully, from any starting stack. -/
theorem BitcoinScript.op_count_fails (f : Flags) (o : Oracle) (stack : List Bytes) (script : Script)
    (h : BitcoinScript.MAX_OPS_PER_SCRIPT < BitcoinScript.opsIn script) :
    BitcoinScript.evalScript f o stack script = none := by
  unfold evalScript
  cases hr : run f o (State.initial stack) script with
  | none => rfl
  | some s' =>
    exfalso
    have := run_opCount f o script _ s' hr
    simp only [State.initial] at this
    have h2 := this.2 (by omega)
    omega
