import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_lineage {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (srcD srcE : NodeId) (sD sE : ClusterState V) (ptD ptE : Nat) (pvD pvE : Int)
    (hD : W.sent (.publishRequest srcD sD ptD pvD)) (hE : W.sent (.publishRequest srcE sE ptE pvE))
    (h : Descends W sD.term sD.version sE.term sE.version)
    (hne : ¬ (sD.term = sE.term ∧ sD.version = sE.version))
    (hint : ∀ ft fv, Committed W ft fv → Descends W sD.term sD.version ft fv → Descends W ft fv sE.term sE.version →
      (ft = sD.term ∧ fv = sD.version) ∨ (ft = sE.term ∧ fv = sE.version)) :
    sE.lastCommittedConfiguration = sD.lastAcceptedConfiguration ∨
    sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration := by sorry
