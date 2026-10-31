import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleCommit_spec {V : Type} (cs : CoordinationState V) (c : ApplyCommitRequest) (cs' : CoordinationState V)
    (h : cs.handleCommit c = .ok cs') :
    c.term = cs.currentTerm ∧ c.term = cs.lastAcceptedTerm ∧ c.version = cs.lastAcceptedVersion ∧
    cs' = { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted } ∧
    cs'.lastCommittedConfiguration = cs'.lastAcceptedConfiguration ∧
    cs'.lastAcceptedConfiguration = cs.lastAcceptedConfiguration ∧
    cs'.lastAcceptedTerm = cs.lastAcceptedTerm ∧ cs'.lastAcceptedVersion = cs.lastAcceptedVersion ∧
    cs'.lastAcceptedState.value = cs.lastAcceptedState.value := by sorry
