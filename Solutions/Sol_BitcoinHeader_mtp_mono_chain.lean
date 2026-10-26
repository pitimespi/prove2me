import Definitions.Def_BitcoinHeader
import Theorems.Thm_BitcoinHeader_mtp_mono

open BitcoinHeader

/-- Along a chain in which every block satisfies the `time-too-old` rule against its
predecessor, the median time past is non-decreasing. -/
theorem solution (times : List Int)
    (hok : ∀ (i : Nat) (hi : i < times.length),
      BitcoinHeader.medianTimePast (times.drop (i + 1)) < times[i]) :
    ∀ (i j : Nat), i ≤ j → j ≤ times.length →
      BitcoinHeader.medianTimePast (times.drop j) ≤ BitcoinHeader.medianTimePast (times.drop i) := by
  intro i j hij hj
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Int.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hj' : j < times.length := by omega
      have step : medianTimePast (times.drop (j + 1)) ≤ medianTimePast (times.drop j) := by
        rw [List.drop_eq_getElem_cons hj']
        exact BitcoinHeader.mtp_mono _ _ (hok j hj')
      exact Int.le_trans step (ih (by omega) (by omega))
    · have : i = j + 1 := by omega
      subst this; exact Int.le_refl _
