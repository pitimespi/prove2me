import Definitions.Def_OpenSearchCoordination

/-!
# OpenSearch cluster coordination: pre-voting and election scheduling

Before a node starts an election it runs a **pre-voting round** (`PreVoteCollector`, OpenSearch
`b2a54ba5c0defba3d1d20423e911d4bf920bab19`,
`server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java`, cited `PVC:<line>`): it asks the nodes
it has discovered, including itself, for a pre-vote. A node answers with its current term and the term and version of
its last accepted state, unless it is unhealthy or already follows a leader other than the requester. The round counts
the answers that are no fresher than the requester's own accepted state, and when they form an election quorum the
requester starts an election (`Coordinator.startElection`, Coordinator.java, cited `CO:<line>`): it sends a
`StartJoinRequest` in a term above every term it has seen. Pre-voting rounds are started by an **election scheduler**
(`ElectionSchedulerFactory`, cited `ESF:<line>`) at randomized, backed-off intervals.

The pre-vote messages and handlers are transcribed below as functions. Both handlers first raise the Coordinator's
`maxTermSeen` (`updateMaxTermSeen`, CO:560-581): `handlePreVoteResponse` returns the term it passes; for
`handlePreVoteRequest` it is always the request's term. When `maxTermSeen` exceeds the current term of a leader, the
leader moves to that term and starts an election itself (CO:565-577); that effect is outside these functions.

Node equality: Java's `DiscoveryNode.equals` compares ephemeral ids, which change when a node restarts; here nodes are
compared by id and role. The two agree except between two incarnations of the same node, which Java treats as
different nodes (so a follower of a node's previous incarnation refuses that node's pre-vote request in Java, and
accepts it here).
-/

namespace OpenSearchPreVote

open OpenSearchCoordination

variable {V : Type}

/-- `PreVoteRequest` (PreVoteRequest.java): the requesting node and its current term. -/
structure PreVoteRequest where
  sourceNode : DiscoveryNode
  currentTerm : Nat
  deriving DecidableEq, Repr

/-- `PreVoteResponse` (PreVoteResponse.java): the responder's current term and the term and version (or metadata
version, for a term-0 state) of its last accepted state. -/
structure PreVoteResponse where
  currentTerm : Nat
  lastAcceptedTerm : Nat
  lastAcceptedVersion : Int
  deriving DecidableEq, Repr

/-- `Coordinator.getPreVoteResponse()` (CO:873-879): the response a node gives, computed from its coordination state. -/
def preVoteResponseOf (cs : CoordinationState V) : PreVoteResponse :=
  ⟨cs.currentTerm, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩

/-- The pre-vote collector's state (PVC:79): the known leader (`none` is Java `null`, no known leader) and the node's
own response, both as last set by `update` (PVC:128-131) — `Coordinator` sets the leader to itself when it becomes
leader, to the leader it follows when it becomes a follower, and to `null` when it becomes a candidate (CO:516, 653, 777,
801, 839, 1157). Java's state is `null` before the first `update`; a node answers pre-votes only after it. -/
structure CollectorState where
  leader : Option DiscoveryNode
  response : PreVoteResponse
  deriving DecidableEq, Repr

/-- `PreVoteCollector.handlePreVoteRequest(request)` (PVC:133-163). `healthy` is the node health status
(`nodeHealthService.getHealth()`). A node that knows a leader other than the requester refuses. (Before answering, the
handler calls `updateMaxTermSeen(request.getCurrentTerm())`, PVC:134; see the module documentation.) -/
def handlePreVoteRequest (healthy : Bool) (st : CollectorState) (req : PreVoteRequest) :
    Except String PreVoteResponse :=
  if !healthy then .error "rejecting on unhealthy node"
  else match st.leader with
    | none => .ok st.response
    | some l => if l = req.sourceNode then .ok st.response else .error "rejecting as there is already a leader"

/-- A pre-voting round (`PreVoteCollector.PreVotingRound`, PVC:175-300): the last accepted cluster state of the
requester when the round started, the requester, the pre-votes received so far (Java: a map keyed by sender; the
most recent first here, at most one entry per sender), whether it has started an election, and whether it was closed.
Java takes the requester from the round's cluster state (`clusterState.nodes().getLocalNode()`, PVC:244); the request's
term (PVC:112) is not needed here. -/
structure PreVotingRound (V : Type) where
  clusterState : ClusterState V
  localNode : DiscoveryNode
  preVotesReceived : List (DiscoveryNode × PreVoteResponse)
  electionStarted : Bool
  isClosed : Bool

/-- `PreVoteCollector.start` (PVC:111-115): a new, open round over the requester's last accepted state. -/
def PreVotingRound.start (s : ClusterState V) (localNode : DiscoveryNode) : PreVotingRound V :=
  ⟨s, localNode, [], false, false⟩

/-- The `VoteCollection` the round builds from its pre-votes (PVC:242-257): `addJoinVote` of a join from each sender,
which counts the cluster-manager-eligible senders. -/
def PreVotingRound.votes (r : PreVotingRound V) : VoteCollection :=
  r.preVotesReceived.foldr (fun p v => (v.addVote p.1).1) VoteCollection.empty

/-- `ElectionStrategy.isElectionQuorum` (ElectionStrategy.java:68-88), as called with explicit arguments. -/
def isElectionQuorumFor (es : ElectionStrategy) (localNode : DiscoveryNode) (currentTerm acceptedTerm : Nat)
    (acceptedVersion : Int) (committed accepted : VotingConfiguration) (votes : VoteCollection) : Bool :=
  votes.isQuorum committed && votes.isQuorum accepted &&
    es.satisfiesAdditionalQuorumConstraints localNode currentTerm acceptedTerm acceptedVersion committed accepted votes

/-- `PreVotingRound.handlePreVoteResponse(response, sender)` (PVC:225-279). `localResponse` is the requester's own
current response (`getPreVoteResponse()`, read when the response arrives). Returns the new round, whether
`startElection` is called, and the argument of the `updateMaxTermSeen` call (`none` when the round is closed and the
response is ignored before it). A response fresher than the round's accepted state is ignored. -/
def PreVotingRound.handlePreVoteResponse (es : ElectionStrategy) (localResponse : PreVoteResponse)
    (r : PreVotingRound V) (resp : PreVoteResponse) (sender : DiscoveryNode) :
    PreVotingRound V × Bool × Option Nat :=
  if r.isClosed then (r, false, none)
  else if resp.lastAcceptedTerm > r.clusterState.term ∨
      (resp.lastAcceptedTerm = r.clusterState.term ∧
        resp.lastAcceptedVersion > r.clusterState.versionOrMetadataVersion) then
    (r, false, some resp.currentTerm)
  else
    let r₁ : PreVotingRound V :=
      { r with preVotesReceived := (sender, resp) :: r.preVotesReceived.filter (fun p => p.1 ≠ sender) }
    if !isElectionQuorumFor es r.localNode localResponse.currentTerm localResponse.lastAcceptedTerm
        localResponse.lastAcceptedVersion r.clusterState.lastCommittedConfiguration
        r.clusterState.lastAcceptedConfiguration r₁.votes then
      (r₁, false, some resp.currentTerm)
    else if r₁.electionStarted then
      (r₁, false, some resp.currentTerm)
    else
      ({ r₁ with electionStarted := true }, true, some resp.currentTerm)

/-- `PreVotingRound.close()` (PVC:296-299). -/
def PreVotingRound.close (r : PreVotingRound V) : PreVotingRound V := { r with isClosed := true }

/-- A pre-vote response is no fresher than the accepted state `s`: its accepted (term, version) is lexicographically at
most `s`'s (term, version-or-metadata-version) — the responses a round counts (PVC:232-238). -/
def NoFresher (resp : PreVoteResponse) (s : ClusterState V) : Prop :=
  resp.lastAcceptedTerm < s.term ∨
    (resp.lastAcceptedTerm = s.term ∧ resp.lastAcceptedVersion ≤ s.versionOrMetadataVersion)

/-- The rounds a node can be in: started over its accepted state, then any sequence of responses handled — each
response from a sender and with a content allowed by `Delivered` — and possibly closed. `localResponse` (the requester's
own current response) is arbitrary at each step. -/
inductive RoundReachable (es : ElectionStrategy) (Delivered : DiscoveryNode → PreVoteResponse → Prop) :
    PreVotingRound V → Prop where
  | start (s : ClusterState V) (n : DiscoveryNode) : RoundReachable es Delivered (PreVotingRound.start s n)
  | handle (r : PreVotingRound V) (localResponse resp : PreVoteResponse) (sender : DiscoveryNode) :
      RoundReachable es Delivered r → Delivered sender resp →
      RoundReachable es Delivered (r.handlePreVoteResponse es localResponse resp sender).1
  | close (r : PreVotingRound V) : RoundReachable es Delivered r → RoundReachable es Delivered r.close

/-- The joins a node handles, in the order given, as `Coordinator.handleJoin` (CO:1267-1299) does for joins whose term is
not above the node's current term (for a higher term it first moves the node to that term, CO:1269). A rejected join
leaves the state unchanged: `handleJoin` throws before changing anything, and `Coordinator.handleJoin` either
propagates the exception to the joining node or ignores it. -/
def handleJoins (es : ElectionStrategy) (cs : CoordinationState V) (js : List Join) : CoordinationState V :=
  js.foldl (fun cs j => match cs.handleJoin es j with
    | .ok (cs', _) => cs'
    | .error _ => cs) cs

/-- The term of the election `Coordinator.startElection` starts (CO:583-602): one above the larger of the current term
and the largest term seen. -/
def startElectionTerm (currentTerm maxTermSeen : Nat) : Nat := max currentTerm maxTermSeen + 1

/-- `Coordinator.nodeMayWinElection` (CO:628-633): the node is in the last committed or last accepted configuration,
or it is not excluded from voting. `excluded` lists the node ids of the voting-configuration exclusions. -/
def nodeMayWinElection (s : ClusterState V) (excluded : List NodeId) (n : NodeId) : Bool :=
  s.lastCommittedConfiguration.nodeIds.contains n || s.lastAcceptedConfiguration.nodeIds.contains n ||
    !(excluded.contains n)

/-! ## Election scheduling (`ElectionSchedulerFactory`) -/

/-- The scheduler settings, in milliseconds (ESF:85-115): `cluster.election.initial_timeout` (default 100, range
1..10000), `cluster.election.back_off_time` (default 100, range 1..60000), `cluster.election.max_timeout` (default 10000,
range 200..300000, at least the initial timeout), `cluster.election.duration` (default 500, range 1..300000). -/
structure SchedulerSettings where
  initialTimeout : Nat
  backoffTime : Nat
  maxTimeout : Nat
  duration : Nat

/-- The settings' validity (setting bounds, ESF:85-115, and the constructor check, ESF:133-143). -/
def SchedulerSettings.Valid (s : SchedulerSettings) : Prop :=
  1 ≤ s.initialTimeout ∧ s.initialTimeout ≤ 10000 ∧ 1 ≤ s.backoffTime ∧ s.backoffTime ≤ 60000 ∧
  200 ≤ s.maxTimeout ∧ s.maxTimeout ≤ 300000 ∧ s.initialTimeout ≤ s.maxTimeout ∧ 1 ≤ s.duration ∧ s.duration ≤ 300000

/-- The defaults. -/
def SchedulerSettings.default : SchedulerSettings := ⟨100, 100, 10000, 500⟩

/-- The bound on the delay of attempt `k` (ESF:203): `min(maxTimeout, initialTimeout + k * backoffTime)`. -/
def maxDelay (s : SchedulerSettings) (k : Nat) : Nat := min s.maxTimeout (s.initialTimeout + k * s.backoffTime)

/-- `nonNegative(n)` (ESF:159-161) on a Java `long` `n ∈ [-2^63, 2^63)`: `Long.MIN_VALUE` maps to 0, others to `|n|`. -/
def nonNegative (n : Int) : Nat := if n = -2 ^ 63 then 0 else n.natAbs

/-- `toPositiveLongAtMost(randomNumber, upperBound)` (ESF:169-172): `nonNegative(randomNumber) % upperBound + 1`. -/
def toPositiveLongAtMost (randomNumber : Int) (upperBound : Nat) : Nat := nonNegative randomNumber % upperBound + 1

/-- The delay before attempt `k` fires, given the random long drawn for it and the grace period (ESF:195-204):
the grace period is 0 for the first attempt (`Coordinator.startElectionScheduler`, CO:1574) and `duration` for every later
one (ESF:218). -/
def attemptDelay (s : SchedulerSettings) (k : Nat) (randomNumber : Int) (gracePeriod : Nat) : Nat :=
  toPositiveLongAtMost randomNumber (maxDelay s k) + gracePeriod

end OpenSearchPreVote
