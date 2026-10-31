import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_first_committed {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) (hc : Committed W t v) :
    ∃ et ev, Committed W et ev ∧ Descends W et ev t v ∧
      ∀ ft fv, Committed W ft fv → Descends W ft fv et ev → ft = et ∧ fv = ev := by sorry
