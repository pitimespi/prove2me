import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.javaInvariant_preserved {V : Type} (es : ElectionStrategy) (hes : es.Monotone) (cs : CoordinationState V)
    (hinv : cs.javaInvariant es) :
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.javaInvariant es) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.javaInvariant es) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.javaInvariant es) := by sorry
