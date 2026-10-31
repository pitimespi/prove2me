import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_respond {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n src : NodeId) (r : PublishResponse) (cs' : CoordinationState V) (o : Option ApplyCommitRequest)
    (hsent : W.sent (.publishResponse src n r)) (h : (W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)) :
    Inv P (match o with
      | none => W.set n cs'
      | some c => (W.set n cs').send (.applyCommit c)) := by sorry
