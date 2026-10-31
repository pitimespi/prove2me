import Definitions.Def_OpenSearchSafety
open OpenSearchCoordination OpenSearchSafety

theorem OpenSearchSafety.inv_startJoin {V : Type} (P : Params) (_hP : P.InitCompatible)
    (_hes : P.strategy = ElectionStrategy.DEFAULT_INSTANCE) (W : Cluster V) (hinv : Inv P W)
    (n src : NodeId) (t : Nat) (cs' : CoordinationState V) (j : Join) (hsrc : P.eligible src = true)
    (h : (W.node n).handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)) : Inv P ((W.set n cs').send (.join j)) := by sorry
