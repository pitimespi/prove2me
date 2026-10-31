import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_descends_linear {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (t₁ t₂ t : Nat) (v₁ v₂ v : Int) (h₁ : Descends W t₁ v₁ t v) (h₂ : Descends W t₂ v₂ t v) :
    Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁ := by sorry
