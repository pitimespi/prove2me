import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_elc {V : Type} (P : Params) (hP : P.InitCompatible) (W : Cluster V) (hinv : Inv P W)
    (L : NodeId) (t bt : Nat) (bv : Int) (x y : VotingConfiguration) (J : List NodeId)
    (hrec : ElectionRecord P W L t bt bv x y J) (ct : Nat) (cv : Int) (hc : Committed W ct cv) (hlt : ct < t) :
    Descends W ct cv bt bv := by sorry
