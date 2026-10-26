import Definitions.Def_BitcoinHeader

open BitcoinHeader

theorem solution (times : List Int) (h : times ≠ []) :
    BitcoinHeader.medianTimePast times ∈ BitcoinHeader.timeWindow times := by
  unfold medianTimePast
  simp only []
  generalize hw : timeWindow times = w
  have hwne : w ≠ [] := by
    intro hnil
    unfold timeWindow at hw
    rw [hnil] at hw
    have := congrArg List.length hw
    simp only [List.length_take, List.length_nil] at this
    have hpos : 0 < times.length := List.length_pos_iff.2 h
    unfold nMedianTimeSpan at this
    omega
  have hpos : 0 < w.length := List.length_pos_iff.2 hwne
  generalize hs : (w.mergeSort fun a b => decide (a ≤ b)) = s
  have hperm : s.Perm w := hs ▸ List.mergeSort_perm w _
  have hlen : s.length = w.length := hperm.length_eq
  have hk : w.length / 2 < s.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact hperm.mem_iff.1 (List.getElem_mem hk)
