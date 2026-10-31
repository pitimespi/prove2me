import Definitions.Def_OpenSearchCoordination

theorem OpenSearchCoordination.handleJoin_spec {V : Type} (es : ElectionStrategy) (cs : CoordinationState V) (j : Join) (cs' : CoordinationState V)
    (b : Bool) (h : cs.handleJoin es j = .ok (cs', b)) :
    j.term = cs.currentTerm ∧ cs.startedJoinSinceLastReboot = true ∧
    cs.lastAcceptedConfiguration.isEmpty = false ∧
    (j.lastAcceptedTerm < cs.lastAcceptedTerm ∨
      (j.lastAcceptedTerm = cs.lastAcceptedTerm ∧ j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion)) ∧
    cs'.joinVotes = (cs.joinVotes.addVote j.sourceNode).1 ∧ b = (cs.joinVotes.addVote j.sourceNode).2 ∧
    cs'.electionWon = cs.isElectionQuorum es cs'.joinVotes ∧
    cs'.currentTerm = cs.currentTerm ∧ cs'.lastAcceptedState = cs.lastAcceptedState ∧
    cs'.localNode = cs.localNode ∧ cs'.startedJoinSinceLastReboot = cs.startedJoinSinceLastReboot ∧
    cs'.publishVotes = cs.publishVotes ∧ cs'.lastPublishedConfiguration = cs.lastPublishedConfiguration ∧
    cs'.lastPublishedVersion =
      (if cs'.electionWon = true ∧ cs.electionWon = false then cs.lastAcceptedVersion else cs.lastPublishedVersion) := by sorry
