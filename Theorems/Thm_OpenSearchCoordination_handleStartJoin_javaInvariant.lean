import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleStartJoin_javaInvariant {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (r : StartJoinRequest)
    (cs' : CoordinationState V) (j : Join) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handleStartJoin r = .ok (cs', j)) : cs'.javaInvariant es := by sorry
