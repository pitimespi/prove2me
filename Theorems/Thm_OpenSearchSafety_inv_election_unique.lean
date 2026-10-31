import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_election_unique {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V)
    (hinv : Inv P W) (t : Nat) (L₁ L₂ : NodeId) (bt₁ bt₂ : Nat) (bv₁ bv₂ : Int)
    (x₁ y₁ x₂ y₂ : VotingConfiguration) (J₁ J₂ : List NodeId)
    (h₁ : ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁) (h₂ : ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂) :
    L₁ = L₂ := by sorry
