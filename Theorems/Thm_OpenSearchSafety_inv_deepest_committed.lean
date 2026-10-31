import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_deepest_committed {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t : Nat) (v : Int) :
    (∃ dt dv, Committed W dt dv ∧ Descends W dt dv t v ∧
      ∀ et ev, Committed W et ev → Descends W et ev t v → Descends W et ev dt dv) ∨
    (∀ et ev, Committed W et ev → ¬ Descends W et ev t v) := by sorry
