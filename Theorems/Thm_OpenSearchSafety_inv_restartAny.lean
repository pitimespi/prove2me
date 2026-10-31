import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_restartAny {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (t : Nat) (s' : ClusterState V) (hn : P.eligible n = false) :
    Inv P (W.set n (CoordinationState.init (W.node n).localNode t s')) := by sorry
