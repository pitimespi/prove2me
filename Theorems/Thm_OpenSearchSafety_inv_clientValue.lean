import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_clientValue {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n : NodeId) (s : ClusterState V) (cs' : CoordinationState V) (p : PublishRequest V)
    (hcontract : (W.node n).clientValueContract s) (h : (W.node n).handleClientValue s = .ok (cs', p)) :
    Inv P ((W.set n cs').send (.publishRequest n p.acceptedState (W.node n).lastAcceptedTerm
      (W.node n).lastAcceptedVersion)) := by sorry
