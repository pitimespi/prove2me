import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_join {V : Type} (P : Params) (hP : P.InitCompatible)
    (hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (j : Join) (cs' : CoordinationState V) (b : Bool) (hsent : W.sent (.join j))
    (hdest : j.targetNode.id = n) (h : (W.node n).handleJoin P.strategy j = .ok (cs', b)) :
    Inv P (W.set n cs') := by sorry
