import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_descends_key {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t t' : Nat) (v v' : Int) (h : Descends W t v t' v') :
    (t = t' ∧ v = v') ∨ (t ≤ t' ∧ v < v') := by sorry
