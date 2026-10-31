import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_reign_first {V : Type} (P : Params) (W : Cluster V) (hinv : Inv P W)
    (src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (hs : W.sent (.publishRequest src s pt pv)) :
    ∃ src' s' pt' pv', W.sent (.publishRequest src' s' pt' pv') ∧ s'.term = s.term ∧ pt' < s'.term ∧
      Descends W s'.term s'.version s.term s.version := by sorry
