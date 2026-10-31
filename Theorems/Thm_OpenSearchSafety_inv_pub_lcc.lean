import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_pub_lcc {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) :
    P.initConfs s.lastCommittedConfiguration ∨
    ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ Committed W s'.term s'.version ∧
      s'.lastAcceptedConfiguration = s.lastCommittedConfiguration := by sorry
