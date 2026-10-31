import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_restart {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (s' : ClusterState V) (hn : P.eligible n = true)
    (hs : RestartState (W.node n).lastAcceptedState s') :
    Inv P (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s')) := by sorry
