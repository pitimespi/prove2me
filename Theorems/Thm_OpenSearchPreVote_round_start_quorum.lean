import Definitions.Def_OpenSearchPreVote
open OpenSearchCoordination OpenSearchPreVote

theorem OpenSearchPreVote.round_start_quorum {V : Type} (es : ElectionStrategy) (lr resp : PreVoteResponse)
    (sender : DiscoveryNode) (r r' : PreVotingRound V) (m : Option Nat)
    (h : r.handlePreVoteResponse es lr resp sender = (r', true, m)) :
    r.isClosed = false ∧ r.electionStarted = false ∧ r'.electionStarted = true ∧ NoFresher resp r.clusterState ∧
    r'.clusterState = r.clusterState ∧ r'.localNode = r.localNode ∧
    isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion
      r.clusterState.lastCommittedConfiguration r.clusterState.lastAcceptedConfiguration r'.votes = true := by sorry
