import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.descends_trans {V : Type} (W : Cluster V) (t₁ t₂ t₃ : Nat) (v₁ v₂ v₃ : Int)
    (h₁ : Descends W t₁ v₁ t₂ v₂) (h₂ : Descends W t₂ v₂ t₃ v₃) : Descends W t₁ v₁ t₃ v₃ := by sorry
