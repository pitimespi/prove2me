import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handlePublishRequest_spec {V : Type} (cs : CoordinationState V) (req : PublishRequest V) (cs' : CoordinationState V)
    (resp : PublishResponse) (hcs : cs.lastAcceptedTerm ≤ cs.currentTerm)
    (h : cs.handlePublishRequest req = .ok (cs', resp)) :
    cs'.lastAcceptedState = req.acceptedState ∧ req.acceptedState.term = cs.currentTerm ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.localNode = cs.localNode ∧
    resp = ⟨req.acceptedState.term, req.acceptedState.version⟩ ∧
    (cs.lastAcceptedTerm < req.acceptedState.term ∨
      (cs.lastAcceptedTerm = req.acceptedState.term ∧ cs.lastAcceptedVersion < req.acceptedState.version) ∨
      req.acceptedState.term = ZEN1_BWC_TERM) ∧
    cs'.joinVotes = cs.joinVotes ∧ cs'.electionWon = cs.electionWon ∧
    cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    cs'.lastPublishedVersion = cs.lastPublishedVersion ∧
    cs'.lastPublishedConfiguration = cs.lastPublishedConfiguration ∧ cs'.publishVotes = cs.publishVotes := by sorry
