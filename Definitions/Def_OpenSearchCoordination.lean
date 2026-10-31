/-!
# OpenSearch cluster coordination: `CoordinationState`

Transcription of the per-node consensus state machine of OpenSearch's cluster coordination ("Zen2"),
`org.opensearch.cluster.coordination.CoordinationState`, at OpenSearch revision
`b2a54ba5c0defba3d1d20423e911d4bf920bab19`
(`server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java`, cited below as `CS:<line>`),
with the parts of `CoordinationMetadata.VotingConfiguration` (`CM:<line>`), `ElectionStrategy` (`ES:<line>`),
`ClusterState` (`CLS:<line>`) and the message classes that it reads.

Abstractions:
* Node ids are `Nat` (Java: `String`); only equality is used.
* Terms are `Nat`: the persisted term starts at `0` and only `handleStartJoin` changes it, to a strictly larger value.
* Versions are `Int` (Java `long`).
* A `ClusterState` is reduced to the fields that `CoordinationState` reads or writes; everything else is an opaque
  payload `value : V`.
* `VotingConfiguration` stores its node ids strictly sorted, so that `=` is Java's `Set.equals`.
* The REMOTE persisted state (remote cluster-state store) is written but never read by these handlers (every read is
  of the LOCAL persisted state), so it is omitted.
* Java `assert`s are not checked in production; they are caller contracts. The handlers below do not check them; the
  cluster model states them as preconditions of the corresponding steps.
-/

namespace OpenSearchCoordination

/-- A node id (`DiscoveryNode.getId()`). -/
abbrev NodeId := Nat

/-- `DiscoveryNode`, as far as coordination reads it: the node id and whether the node has the cluster-manager
(master-eligible) role (`DiscoveryNode.isClusterManagerNode()`). -/
structure DiscoveryNode where
  id : NodeId
  isClusterManagerNode : Bool
  deriving DecidableEq, Repr

/-- `Coordinator.ZEN1_BWC_TERM` (Coordinator.java:134). -/
def ZEN1_BWC_TERM : Nat := 0

/-! ## Voting configurations and vote collections -/

/-- `CoordinationMetadata.VotingConfiguration` (CM:380-450): a set of node ids. Stored strictly sorted, so that
structural equality is set equality (Java `equals` compares the `Set<String> nodeIds`). -/
structure VotingConfiguration where
  nodeIds : List NodeId
  sorted : nodeIds.Pairwise (· < ·)

instance : DecidableEq VotingConfiguration := fun a b =>
  if h : a.nodeIds = b.nodeIds then isTrue (by cases a; cases b; simp at h; subst h; rfl)
  else isFalse (by intro e; exact h (e ▸ rfl))

namespace VotingConfiguration

/-- `VotingConfiguration.EMPTY_CONFIG` (CM:385). -/
def EMPTY_CONFIG : VotingConfiguration := ⟨[], List.Pairwise.nil⟩

/-- `isEmpty()` (CM:433-435). -/
def isEmpty (c : VotingConfiguration) : Bool := c.nodeIds.isEmpty

/-- `hasQuorum(votes)` (CM:405-409): `intersection.size() * 2 > nodeIds.size()` where `intersection` is
`nodeIds ∩ votes`. -/
def hasQuorum (c : VotingConfiguration) (votes : List NodeId) : Bool :=
  decide ((c.nodeIds.filter (fun x => votes.contains x)).length * 2 > c.nodeIds.length)

end VotingConfiguration

/-- `CoordinationState.VoteCollection` (CS:745-815): the ids of the nodes whose votes were added. (Java keys a
`Map<String, DiscoveryNode>` by node id and also records the `Join`s in a set that only tests read.) -/
structure VoteCollection where
  nodes : List NodeId
  deriving DecidableEq, Repr

namespace VoteCollection

/-- `new VoteCollection()`. -/
def empty : VoteCollection := ⟨[]⟩

/-- `addVote(sourceNode)` (CS:751-753): `sourceNode.isClusterManagerNode() && nodes.put(id, sourceNode) == null`. The
new collection and whether the vote was added. -/
def addVote (v : VoteCollection) (n : DiscoveryNode) : VoteCollection × Bool :=
  if n.isClusterManagerNode && !(v.nodes.contains n.id) then (⟨n.id :: v.nodes⟩, true) else (v, false)

/-- `isQuorum(configuration)` (CS:770-772). -/
def isQuorum (v : VoteCollection) (c : VotingConfiguration) : Bool := c.hasQuorum v.nodes

/-- `containsVoteFor(node)` (CS:774-776). -/
def containsVoteFor (v : VoteCollection) (n : DiscoveryNode) : Bool := v.nodes.contains n.id

/-- `isEmpty()` (CS:778-780). -/
def isEmpty (v : VoteCollection) : Bool := v.nodes.isEmpty

end VoteCollection

/-! ## Cluster states, persisted state, messages -/

/-- A cluster state, reduced to what `CoordinationState` reads or writes. -/
structure ClusterState (V : Type) where
  /-- `term()` (= `coordinationMetadata().term()`). -/
  term : Nat
  /-- `version()`. -/
  version : Int
  /-- `metadata().version()`. -/
  metadataVersion : Int
  /-- `getLastCommittedConfiguration()`. -/
  lastCommittedConfiguration : VotingConfiguration
  /-- `getLastAcceptedConfiguration()`. -/
  lastAcceptedConfiguration : VotingConfiguration
  /-- `nodes().getClusterManagerNode()`, identified by its ephemeral id (`DiscoveryNode.equals` compares ephemeral
  ids); `none` is Java `null`. Read only by the Zen1 compatibility branch of `handlePublishRequest`. -/
  clusterManagerNode : Option Nat
  /-- `metadata().clusterUUID()` differs from `Metadata.UNKNOWN_CLUSTER_UUID`. -/
  clusterUUIDKnown : Bool
  /-- `metadata().clusterUUIDCommitted()`. -/
  clusterUUIDCommitted : Bool
  /-- Everything else. -/
  value : V

namespace ClusterState

variable {V : Type}

/-- `getVersionOrMetadataVersion()` (CLS:239-244). -/
def versionOrMetadataVersion (s : ClusterState V) : Int :=
  if s.term = ZEN1_BWC_TERM then s.metadataVersion else s.version

/-- `PersistedState.markLastAcceptedStateAsCommitted()` (CS:648-680) with `commitVotingConfiguration` (CS:682-693):
the committed configuration becomes the accepted one, and a known cluster UUID is marked committed. -/
def markCommitted (s : ClusterState V) : ClusterState V :=
  let s₁ := if s.lastAcceptedConfiguration ≠ s.lastCommittedConfiguration then
      { s with lastCommittedConfiguration := s.lastAcceptedConfiguration } else s
  if s₁.clusterUUIDKnown && !s₁.clusterUUIDCommitted then { s₁ with clusterUUIDCommitted := true } else s₁

end ClusterState

/-- `StartJoinRequest` (StartJoinRequest.java). -/
structure StartJoinRequest where
  sourceNode : DiscoveryNode
  term : Nat
  deriving DecidableEq, Repr

/-- `Join` (Join.java): a vote from `sourceNode` for `targetNode` in `term`, with the voter's last accepted term and
version (or metadata version, for term-0 states). -/
structure Join where
  sourceNode : DiscoveryNode
  targetNode : DiscoveryNode
  term : Nat
  lastAcceptedTerm : Nat
  lastAcceptedVersion : Int
  deriving DecidableEq, Repr

/-- `PublishRequest` (PublishRequest.java). -/
structure PublishRequest (V : Type) where
  acceptedState : ClusterState V

/-- `PublishResponse` (PublishResponse.java). -/
structure PublishResponse where
  term : Nat
  version : Int
  deriving DecidableEq, Repr

/-- `ApplyCommitRequest` (ApplyCommitRequest.java). -/
structure ApplyCommitRequest where
  sourceNode : DiscoveryNode
  term : Nat
  version : Int
  deriving DecidableEq, Repr

/-- `ElectionStrategy` (ES): `isElectionQuorum` is final; plugins override only
`satisfiesAdditionalQuorumConstraints(localNode, currentTerm, acceptedTerm, acceptedVersion, lastCommitted,
lastAccepted, joinVotes)`. -/
structure ElectionStrategy where
  satisfiesAdditionalQuorumConstraints :
    DiscoveryNode → Nat → Nat → Int → VotingConfiguration → VotingConfiguration → VoteCollection → Bool

/-- `ElectionStrategy.DEFAULT_INSTANCE`: no additional constraint. -/
def ElectionStrategy.DEFAULT_INSTANCE : ElectionStrategy := ⟨fun _ _ _ _ _ _ _ => true⟩

/-- An election strategy whose additional constraint is monotone in the votes (adding votes never turns a satisfied
constraint into an unsatisfied one). The default strategy is. -/
def ElectionStrategy.Monotone (es : ElectionStrategy) : Prop :=
  ∀ n t at' av c a (v w : VoteCollection), (∀ x, x ∈ v.nodes → x ∈ w.nodes) →
    es.satisfiesAdditionalQuorumConstraints n t at' av c a v = true →
    es.satisfiesAdditionalQuorumConstraints n t at' av c a w = true

/-! ## The state machine -/

/-- The fields of `CoordinationState` (CS:64-106): the LOCAL persisted state (current term, last accepted cluster
state) and the transient state that a restart discards. -/
structure CoordinationState (V : Type) where
  localNode : DiscoveryNode
  /-- persisted: `getCurrentTerm()` -/
  currentTerm : Nat
  /-- persisted: `getLastAcceptedState()` -/
  lastAcceptedState : ClusterState V
  joinVotes : VoteCollection
  startedJoinSinceLastReboot : Bool
  electionWon : Bool
  lastPublishedVersion : Int
  lastPublishedConfiguration : VotingConfiguration
  publishVotes : VoteCollection

namespace CoordinationState

variable {V : Type}

/-- The constructor (CS:84-106): a fresh `CoordinationState` over a persisted state. A restart. -/
def init (localNode : DiscoveryNode) (currentTerm : Nat) (lastAcceptedState : ClusterState V) :
    CoordinationState V where
  localNode := localNode
  currentTerm := currentTerm
  lastAcceptedState := lastAcceptedState
  joinVotes := VoteCollection.empty
  startedJoinSinceLastReboot := false
  electionWon := false
  lastPublishedVersion := 0
  lastPublishedConfiguration := lastAcceptedState.lastAcceptedConfiguration
  publishVotes := VoteCollection.empty

def lastAcceptedTerm (cs : CoordinationState V) : Nat := cs.lastAcceptedState.term
def lastAcceptedVersion (cs : CoordinationState V) : Int := cs.lastAcceptedState.version
def lastAcceptedVersionOrMetadataVersion (cs : CoordinationState V) : Int :=
  cs.lastAcceptedState.versionOrMetadataVersion
def lastCommittedConfiguration (cs : CoordinationState V) : VotingConfiguration :=
  cs.lastAcceptedState.lastCommittedConfiguration
def lastAcceptedConfiguration (cs : CoordinationState V) : VotingConfiguration :=
  cs.lastAcceptedState.lastAcceptedConfiguration

/-- `isElectionQuorum(joinVotes)` (CS:144-154, ES:66-89). -/
def isElectionQuorum (es : ElectionStrategy) (cs : CoordinationState V) (votes : VoteCollection) : Bool :=
  votes.isQuorum cs.lastCommittedConfiguration && votes.isQuorum cs.lastAcceptedConfiguration &&
    es.satisfiesAdditionalQuorumConstraints cs.localNode cs.currentTerm cs.lastAcceptedTerm cs.lastAcceptedVersion
      cs.lastCommittedConfiguration cs.lastAcceptedConfiguration votes

/-- `isPublishQuorum(votes)` (CS:156-158). -/
def isPublishQuorum (cs : CoordinationState V) (votes : VoteCollection) : Bool :=
  votes.isQuorum cs.lastCommittedConfiguration && votes.isQuorum cs.lastPublishedConfiguration

/-- `setInitialState(initialState)` (CS:180-204). The asserted preconditions are `initialStateContract`. -/
def setInitialState (cs : CoordinationState V) (initialState : ClusterState V) :
    Except String (CoordinationState V) :=
  if !cs.lastAcceptedConfiguration.isEmpty then
    .error "initial state already set: last-accepted configuration now nonempty"
  else
    .ok { cs with lastAcceptedState := initialState }

/-- The assertions of `setInitialState` (CS:190-201): the caller's contract. -/
def initialStateContract (cs : CoordinationState V) (initialState : ClusterState V) : Prop :=
  cs.lastAcceptedTerm = 0 ∧ cs.lastCommittedConfiguration.isEmpty ∧ cs.lastPublishedVersion = 0 ∧
  cs.lastPublishedConfiguration.isEmpty ∧ cs.electionWon = false ∧ cs.joinVotes.isEmpty ∧
  cs.publishVotes.isEmpty ∧ initialState.term = 0 ∧ initialState.version = cs.lastAcceptedVersion ∧
  initialState.lastAcceptedConfiguration.isEmpty = false ∧ initialState.lastCommittedConfiguration.isEmpty = false

/-- `handleStartJoin(startJoinRequest)` (CS:213-255). -/
def handleStartJoin (cs : CoordinationState V) (req : StartJoinRequest) :
    Except String (CoordinationState V × Join) :=
  if req.term ≤ cs.currentTerm then
    .error "incoming term not greater than current term"
  else
    let cs' : CoordinationState V :=
      { cs with
        currentTerm := req.term
        lastPublishedVersion := 0
        lastPublishedConfiguration := cs.lastAcceptedConfiguration
        startedJoinSinceLastReboot := true
        electionWon := false
        joinVotes := VoteCollection.empty
        publishVotes := VoteCollection.empty }
    .ok (cs', ⟨cs.localNode, req.sourceNode, req.term, cs.lastAcceptedTerm, cs.lastAcceptedVersionOrMetadataVersion⟩)

/-- `handleJoin(join)` (CS:264-339). Returns whether the vote was new. (Asserted: `join.targetNode` is this node.) -/
def handleJoin (es : ElectionStrategy) (cs : CoordinationState V) (join : Join) :
    Except String (CoordinationState V × Bool) :=
  if join.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if !cs.startedJoinSinceLastReboot then
    .error "ignored join as term has not been incremented yet after reboot"
  else if join.lastAcceptedTerm > cs.lastAcceptedTerm then
    .error "incoming last accepted term of join higher than current last accepted term"
  else if join.lastAcceptedTerm = cs.lastAcceptedTerm ∧
      join.lastAcceptedVersion > cs.lastAcceptedVersionOrMetadataVersion then
    .error "incoming last accepted version of join higher than current last accepted version"
  else if cs.lastAcceptedConfiguration.isEmpty then
    .error "rejecting join since this node has not received its initial configuration yet"
  else
    let (votes, added) := cs.joinVotes.addVote join.sourceNode
    let won := isElectionQuorum es cs votes
    let cs₁ : CoordinationState V := { cs with joinVotes := votes, electionWon := won }
    let cs₂ := if won && !cs.electionWon then { cs₁ with lastPublishedVersion := cs.lastAcceptedVersion } else cs₁
    .ok (cs₂, added)

/-- `handleClientValue(clusterState)` (CS:348-407). The assertion of CS:397-398 is `clientValueContract`. -/
def handleClientValue (cs : CoordinationState V) (clusterState : ClusterState V) :
    Except String (CoordinationState V × PublishRequest V) :=
  if !cs.electionWon then
    .error "election not won"
  else if cs.lastPublishedVersion ≠ cs.lastAcceptedVersion then
    .error "cannot start publishing next value before accepting previous one"
  else if clusterState.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if clusterState.version ≤ cs.lastPublishedVersion then
    .error "incoming cluster state version lower or equal to last published version"
  else if clusterState.lastAcceptedConfiguration ≠ cs.lastAcceptedConfiguration ∧
      cs.lastCommittedConfiguration ≠ cs.lastAcceptedConfiguration then
    .error "only allow reconfiguration while not already reconfiguring"
  else if !cs.joinVotes.isQuorum clusterState.lastAcceptedConfiguration then
    .error "only allow reconfiguration if joinVotes have quorum for new config"
  else
    .ok ({ cs with
            lastPublishedVersion := clusterState.version
            lastPublishedConfiguration := clusterState.lastAcceptedConfiguration
            publishVotes := VoteCollection.empty },
         ⟨clusterState⟩)

/-- The assertion of `handleClientValue` (CS:397-398): the last committed configuration does not change. -/
def clientValueContract (cs : CoordinationState V) (clusterState : ClusterState V) : Prop :=
  clusterState.lastCommittedConfiguration = cs.lastCommittedConfiguration

/-- `handlePublishRequest(publishRequest)` (CS:416-460). In the Zen1 compatibility branch, Java's
`getClusterManagerNode().equals(...)` on a `null` incoming cluster-manager throws (a rejection). -/
def handlePublishRequest (cs : CoordinationState V) (req : PublishRequest V) :
    Except String (CoordinationState V × PublishResponse) :=
  let s := req.acceptedState
  let accept : Except String (CoordinationState V × PublishResponse) :=
    .ok ({ cs with lastAcceptedState := s }, ⟨s.term, s.version⟩)
  if s.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if s.term = cs.lastAcceptedTerm ∧ s.version ≤ cs.lastAcceptedVersion then
    if s.term = ZEN1_BWC_TERM then
      match s.clusterManagerNode with
      | none => .error "NullPointerException"
      | some m =>
        if some m ≠ cs.lastAcceptedState.clusterManagerNode then accept
        else .error "incoming version lower or equal to current version"
    else
      .error "incoming version lower or equal to current version"
  else
    accept

/-- `handlePublishResponse(sourceNode, publishResponse)` (CS:471-515). The optional `ApplyCommitRequest`. -/
def handlePublishResponse (cs : CoordinationState V) (sourceNode : DiscoveryNode) (resp : PublishResponse) :
    Except String (CoordinationState V × Option ApplyCommitRequest) :=
  if !cs.electionWon then
    .error "election not won"
  else if resp.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if resp.version ≠ cs.lastPublishedVersion then
    .error "incoming version does not match current version"
  else
    let votes := (cs.publishVotes.addVote sourceNode).1
    let cs' : CoordinationState V := { cs with publishVotes := votes }
    if isPublishQuorum cs' votes then
      .ok (cs', some ⟨cs.localNode, resp.term, resp.version⟩)
    else
      .ok (cs', none)

/-- `handleCommit(applyCommit)` (CS:522-574). -/
def handleCommit (cs : CoordinationState V) (c : ApplyCommitRequest) : Except String (CoordinationState V) :=
  if c.term ≠ cs.currentTerm then
    .error "incoming term does not match current term"
  else if c.term ≠ cs.lastAcceptedTerm then
    .error "incoming term does not match last accepted term"
  else if c.version ≠ cs.lastAcceptedVersion then
    .error "incoming version does not match current version"
  else
    .ok { cs with lastAcceptedState := cs.lastAcceptedState.markCommitted }

/-- `invariant()` (CS:603-613), the assertions Java checks in tests. -/
def javaInvariant (es : ElectionStrategy) (cs : CoordinationState V) : Prop :=
  cs.lastAcceptedTerm ≤ cs.currentTerm ∧
  cs.electionWon = isElectionQuorum es cs cs.joinVotes ∧
  (if cs.electionWon then cs.lastPublishedVersion ≥ cs.lastAcceptedVersion else cs.lastPublishedVersion = 0) ∧
  (cs.electionWon = true → cs.startedJoinSinceLastReboot = true) ∧
  (cs.publishVotes.isEmpty = true ∨ cs.electionWon = true)

end CoordinationState

end OpenSearchCoordination
