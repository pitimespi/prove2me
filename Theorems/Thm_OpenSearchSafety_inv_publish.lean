import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_publish {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n src : NodeId) (s : ClusterState V) (pt : Nat) (pv : Int) (cs' : CoordinationState V) (r : PublishResponse)
    (hsent : W.sent (.publishRequest src s pt pv)) (h : (W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)) :
    Inv P ((W.set n cs').send (.publishResponse n src r)) := by sorry
