import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_root_lcc {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv))
    (hroot : ∀ ft fv, Committed W ft fv → Descends W ft fv s.term s.version → ft = s.term ∧ fv = s.version) :
    P.initConfs s.lastCommittedConfiguration := by sorry
