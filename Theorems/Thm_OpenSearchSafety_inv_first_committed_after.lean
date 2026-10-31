import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_first_committed_after {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (dt ct : Nat) (dv cv : Int) (h : Descends W dt dv ct cv) (hne : ¬ (dt = ct ∧ dv = cv))
    (hc : Committed W ct cv) :
    ∃ et ev, Committed W et ev ∧ Descends W dt dv et ev ∧ ¬ (dt = et ∧ dv = ev) ∧ Descends W et ev ct cv ∧
      ∀ ft fv, Committed W ft fv → Descends W dt dv ft fv → Descends W ft fv et ev →
        (ft = dt ∧ fv = dv) ∨ (ft = et ∧ fv = ev) := by sorry
