import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.lastAcceptedTerm_le_currentTerm {V : Type} (es : ElectionStrategy) (cs : CoordinationState V)
    (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm) :
    (∀ s cs', cs.setInitialState s = .ok cs' → s.term = 0 → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ r cs' j, cs.handleStartJoin r = .ok (cs', j) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs.currentTerm < cs'.currentTerm) ∧
    (∀ j cs' b, cs.handleJoin es j = .ok (cs', b) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ s cs' p, cs.handleClientValue s = .ok (cs', p) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ p cs' r, cs.handlePublishRequest p = .ok (cs', r) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ n r cs' o, cs.handlePublishResponse n r = .ok (cs', o) → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) ∧
    (∀ c cs', cs.handleCommit c = .ok cs' → cs'.lastAcceptedTerm ≤ cs'.currentTerm ∧
        cs'.currentTerm = cs.currentTerm) := by sorry
