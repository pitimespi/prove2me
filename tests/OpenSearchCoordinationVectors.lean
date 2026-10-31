import Definitions.Def_OpenSearchCoordination

/-!
# OpenSearch's `CoordinationStateTests`, replayed against the transcription

The unit tests of `CoordinationState` (OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19`,
`server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java`, cited as `L<line>`) that
exercise the local coordination logic, and the `hasQuorum` test of `CoordinationMetadataTests.java`, replayed with
concrete values against `Definitions/Def_OpenSearchCoordination.lean`. Every Java assertion is checked by an `example`
proved by `decide`, under a comment quoting it; the block of assertions that opens many tests (winning the election:
`wonAloneOk`, `twoJoinsOk`) is checked by one `example` per test, as are the related parts of
`EqualsHashCodeTestUtils.checkEqualsAndHashCode`.

Not replayed: `testSafety` (a randomized cluster run, covered by proof), and the tests of the REMOTE persisted state and
remote publication (`testHandlePrePublishAndCommitWhenRemoteState{Disabled,Enabled}`,
`testHandlePublishRequestOnFollowerWhenRemotePublicationEnabled`,
`testHandleCommitOnFollowerNodeWhenRemotePublicationEnabled{,WithNullRemotePersistedState}`,
`testRemotePersistedStateResetsForPublicationEnabledAfterLocalPublication`): the transcription omits the REMOTE state.

How the Java fixture is modelled:
* `createNode("nodeK")` is `⟨K, true⟩`: its roles (`BUILT_IN_ROLES`) include cluster-manager.
* The test helper `clusterState(term, version, localNode, lastCommitted, lastAccepted, value)` builds a state whose
  metadata comes from `Metadata.builder()` (metadata version 0) with a random cluster UUID (known, not committed) and
  whose `DiscoveryNodes` have no elected cluster-manager; `value` is the payload (`V := Nat`).
* `ClusterState` has identity equality in Java; the tests compare a state with the one that was stored, which is
  structural equality of the reduced states here.
* Java's random draws (`randomLongBetween`, `randomFrom`, `randomBoolean`, `randomNonNegativeLong`) become 2 to 5
  concrete instances per test, including the bounds of each range; each check holds for all of them.
* A Java call made outside `expectThrows` must not throw: every check first requires the replayed calls before it to
  succeed (`okAnd`), so a rejection that a test expects from its last call cannot come from an earlier one.
* `expectThrows(CoordinationStateRejectedException.class, ...)` whose message `containsString(m)` is `rejects x m`: the
  handler returns `.error e` and `e` contains `m`. A bare `expectThrows` is `isErr x`.
* `expectThrows(AssertionError.class, ...)` relies on a Java `assert`; the transcription does not check `assert`s (they
  are caller contracts), so those assertions are recorded as comments (`testJoinWithWrongTarget`,
  `testHandleClientValueWithIllegalCommittedConfigurationChange`).

Result: every assertion holds, except the copy-equality assertions of `EqualsHashCodeTestUtils.checkEqualsAndHashCode`
in `testVoteCollection` when Java's `VoteCollection.equals` is read as the transcription's `=`: that is list equality,
which depends on the order in which the votes were added, whereas Java compares the maps of voters. Those checks are
commented out below (they hold with set equality of the voters); no handler compares vote collections.
-/

namespace OpenSearchCoordinationVectors

open OpenSearchCoordination

/-! ## Helpers -/

abbrev CS := CoordinationState Nat
abbrev State := ClusterState Nat

-- Structural equality of the reduced cluster states.
deriving instance DecidableEq for ClusterState

/-- A voting configuration from its node ids in increasing order (Java `VotingConfiguration.of(...)`). -/
def cfg (l : List Nat) (h : l.Pairwise (· < ·) := by decide) : VotingConfiguration := ⟨l, h⟩

/-- The handler rejected its input (Java: it threw a `CoordinationStateRejectedException`). -/
def isErr {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

/-- The rejection message (`""` if the input was accepted). -/
def errMsg {α : Type} : Except String α → String
  | .error e => e
  | .ok _ => ""

/-- `p` is a prefix of `s`. -/
def isPrefixL {α : Type} [BEq α] : List α → List α → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: p, b :: s => a == b && isPrefixL p s

/-- `p` occurs in `s`. -/
def isInfixL {α : Type} [BEq α] (p : List α) : List α → Bool
  | [] => p.isEmpty
  | c :: s => isPrefixL p (c :: s) || isInfixL p s

/-- Hamcrest `containsString(sub)`: `sub` occurs in `s`. The UTF-8 bytes are compared, which for valid UTF-8 is the same
as comparing characters (a valid encoding can only match at character boundaries; the messages are ASCII anyway), and
is much cheaper for the kernel than decoding the strings into characters. -/
def containsStr (s sub : String) : Bool := isInfixL sub.toByteArray.data.toList s.toByteArray.data.toList

/-- `expectThrows(CoordinationStateRejectedException.class, ...)` whose message `containsString(sub)`. -/
def rejects {α : Type} (x : Except String α) (sub : String) : Bool := isErr x && containsStr (errMsg x) sub

/-- The replayed calls all succeeded, and `p` holds of their result. -/
def okAnd {α : Type} (x : Except String α) (p : α → Bool) : Bool :=
  match x with
  | .ok a => p a
  | .error _ => false

/-! ## Fixture: `setupNodes` (L104-137) and the static helpers (L1268-1365) -/

/-- `createNode("node1")` (L139-156). -/
def node1 : DiscoveryNode := ⟨1, true⟩
/-- `createNode("node2")` -/
def node2 : DiscoveryNode := ⟨2, true⟩
/-- `createNode("node3")` -/
def node3 : DiscoveryNode := ⟨3, true⟩

/-- `clusterState(term, version, localNode, lastCommittedConfig, lastAcceptedConfig, value)` (L1276-1345). `localNode`
only populates `nodes()`, which has no elected cluster-manager, so it does not reach the reduced state. -/
def clusterState (term : Nat) (version : Int) (_localNode : DiscoveryNode)
    (lastCommittedConfig lastAcceptedConfig : VotingConfiguration) (value : Nat) : State where
  term := term
  version := version
  metadataVersion := 0
  lastCommittedConfiguration := lastCommittedConfig
  lastAcceptedConfiguration := lastAcceptedConfig
  clusterManagerNode := none
  clusterUUIDKnown := true
  clusterUUIDCommitted := false
  value := value

/-- `VotingConfiguration.EMPTY_CONFIG` -/
def EMPTY : VotingConfiguration := VotingConfiguration.EMPTY_CONFIG

/-- `initialStateNode1 = clusterState(0L, 0L, node1, EMPTY_CONFIG, EMPTY_CONFIG, 42L)` (L119) -/
def initialStateNode1 : State := clusterState 0 0 node1 EMPTY EMPTY 42
/-- `initialStateNode2` (L120) -/
def initialStateNode2 : State := clusterState 0 0 node2 EMPTY EMPTY 42
/-- `initialStateNode3` (L121-128) -/
def initialStateNode3 : State := clusterState 0 0 node3 EMPTY EMPTY 42

/-- `cs1 = createCoordinationState(psr1, node1, Settings.EMPTY)` over
`new InMemoryPersistedState(0L, initialStateNode1)` (L130-134). -/
def cs1 : CS := CoordinationState.init node1 0 initialStateNode1
/-- `cs2` (L135) -/
def cs2 : CS := CoordinationState.init node2 0 initialStateNode2
/-- `cs3` (L136) -/
def cs3 : CS := CoordinationState.init node3 0 initialStateNode3

/-- `createCoordinationState` uses `ElectionStrategy.DEFAULT_INSTANCE` (L1273). -/
def ES : ElectionStrategy := ElectionStrategy.DEFAULT_INSTANCE

/-- `VotingConfiguration.of(node1)`: the tests' `initialConfig`. -/
def initialConfig : VotingConfiguration := cfg [1]
/-- `VotingConfiguration.of(node1)`, named `configNode1` in some tests. -/
def configNode1 : VotingConfiguration := cfg [1]
/-- `VotingConfiguration.of(node2)`: `configNode2`, `newConfig`, `newConfig1`. -/
def configNode2 : VotingConfiguration := cfg [2]
/-- `VotingConfiguration.of(node3)`: `newConfig2`. -/
def configNode3 : VotingConfiguration := cfg [3]

/-- `state1 = clusterState(0L, 0L, node1, initialConfig, initialConfig, 42L)`: the bootstrap state of most tests. -/
def state1 : State := clusterState 0 0 node1 initialConfig initialConfig 42

/-! ## Prefixes shared by several tests -/

/-- `cs1.setInitialState(state1); Join v1 = cs1.handleStartJoin(new StartJoinRequest(src, t));` -/
def bootStartJoin (src : DiscoveryNode) (t : Nat) : Except String (CS × Join) := do
  let cs ← cs1.setInitialState state1
  cs.handleStartJoin ⟨src, t⟩

/-- `bootStartJoin node1 t`, then `cs1.handleJoin(v1)`: the state and the result of `handleJoin(v1)`. -/
def wonAlone (t : Nat) : Except String (CS × Bool) := do
  let (cs, v1) ← bootStartJoin node1 t
  cs.handleJoin ES v1

/-- The two assertions that follow `wonAlone t` in the tests: `assertTrue(cs1.handleJoin(v1));
assertTrue(cs1.electionWon());` -/
def wonAloneOk (t : Nat) : Bool := okAnd (wonAlone t) (fun (cs, joined) => joined && cs.electionWon)

/-- `cs1.setInitialState(state1)`; `v1 = cs1.handleStartJoin(sjr)` and `v2 = cs2.handleStartJoin(sjr)` for
`sjr = new StartJoinRequest(node1, t)`; `cs1.handleJoin(v1)`; `cs1.handleJoin(v2)`. (In L706-716, L724-734 and
L798-807, `cs2.handleStartJoin` comes after `cs1.handleJoin(v1)`; `cs1` and `cs2` are independent, so this is the
same run.) -/
structure TwoJoins where
  /-- `cs1` after both joins -/
  leader : CS
  /-- `cs2` after `handleStartJoin(sjr)` -/
  follower : CS
  /-- `cs1.handleJoin(v1)` -/
  joinedV1 : Bool
  /-- `cs1.electionWon()` after `handleJoin(v1)` -/
  wonAfterV1 : Bool
  /-- `cs1.handleJoin(v2)` -/
  joinedV2 : Bool

def twoJoins (t : Nat) : Except String TwoJoins := do
  let (cs, v1) ← bootStartJoin node1 t
  let (follower, v2) ← cs2.handleStartJoin ⟨node1, t⟩
  let (cs, joinedV1) ← cs.handleJoin ES v1
  let wonAfterV1 := cs.electionWon
  let (leader, joinedV2) ← cs.handleJoin ES v2
  return { leader, follower, joinedV1, wonAfterV1, joinedV2 }

/-- The assertions that follow `twoJoins t` in the tests: `assertTrue(cs1.handleJoin(v1));
assertTrue(cs1.electionWon()); assertTrue(cs1.handleJoin(v2));` -/
def twoJoinsOk (t : Nat) : Bool := okAnd (twoJoins t) (fun r => r.joinedV1 && r.wonAfterV1 && r.joinedV2)

/-- `cs1.handleJoin(join)` twice: the state after the first call, and the results of both calls. -/
def joinTwice (cs : CS) (j : Join) : Except String (CS × Bool × Bool) := do
  let (cs, joined) ← cs.handleJoin ES j
  let (_, again) ← cs.handleJoin ES j
  return (cs, joined, again)

/-- `wonAlone t`, then `publishRequest = cs1.handleClientValue(state2)` for
`state2 = clusterState(t, 2L, node1, initialConfig, initialConfig, value)` and
`publishResponse = cs1.handlePublishRequest(publishRequest)`. -/
def publishedOwn (t value : Nat) : Except String (CS × PublishResponse) := do
  let (cs, _) ← wonAlone t
  let (cs, publishRequest) ← cs.handleClientValue (clusterState t 2 node1 initialConfig initialConfig value)
  cs.handlePublishRequest publishRequest

/-! ## testSetInitialState (CoordinationStateTests.java:158) -/

-- L161 assertTrue(state1.getLastAcceptedConfiguration().hasQuorum(Collections.singleton(node1.getId())))
example : state1.lastAcceptedConfiguration.hasQuorum [node1.id] = true := by decide
-- L162 assertTrue(state1.getLastCommittedConfiguration().hasQuorum(Collections.singleton(node1.getId())))
example : state1.lastCommittedConfiguration.hasQuorum [node1.id] = true := by decide
-- L163 cs1.setInitialState(state1); L164 assertThat(cs1.getLastAcceptedState(), equalTo(state1))
example : okAnd (cs1.setInitialState state1) (fun cs => cs.lastAcceptedState == state1) = true := by decide

/-! ## testSetInitialStateWhenAlreadySet (CoordinationStateTests.java:167) -/

-- L170 assertTrue(state1.getLastAcceptedConfiguration().hasQuorum(Collections.singleton(node1.getId())))
example : state1.lastAcceptedConfiguration.hasQuorum [node1.id] = true := by decide
-- L171 assertTrue(state1.getLastCommittedConfiguration().hasQuorum(Collections.singleton(node1.getId())))
example : state1.lastCommittedConfiguration.hasQuorum [node1.id] = true := by decide
-- L172 cs1.setInitialState(state1);
-- L173-176 expectThrows(..., () -> cs1.setInitialState(state1)), containsString("initial state already set")
example : okAnd (cs1.setInitialState state1)
    (fun cs => rejects (cs.setInitialState state1) "initial state already set") = true := by decide

/-! ## testStartJoinBeforeBootstrap (CoordinationStateTests.java:179) -/

/-- `startJoinRequest1 = new StartJoinRequest(randomFrom(node1, node2), randomLongBetween(1, 5))` and
`startJoinRequest2 = new StartJoinRequest(randomFrom(node1, node2),
randomLongBetween(0, startJoinRequest1.getTerm()))`. -/
def startJoinCases : List (DiscoveryNode × Nat × DiscoveryNode × Nat) :=
  [(node1, 1, node2, 0), (node2, 5, node1, 5), (node2, 3, node2, 1), (node1, 2, node1, 2)]

-- L180 assertThat(cs1.getCurrentTerm(), equalTo(0L))
example : (cs1.currentTerm == 0) = true := by decide
-- L182 Join v1 = cs1.handleStartJoin(startJoinRequest1);
-- L183 assertThat(v1.getTargetNode(), equalTo(startJoinRequest1.getSourceNode()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (cs1.handleStartJoin ⟨src, t⟩) (fun (_, v1) => v1.targetNode == src)) = true := by decide
-- L184 assertThat(v1.getSourceNode(), equalTo(node1))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (cs1.handleStartJoin ⟨src, t⟩) (fun (_, v1) => v1.sourceNode == node1)) = true := by decide
-- L185 assertThat(v1.getTerm(), equalTo(startJoinRequest1.getTerm()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (cs1.handleStartJoin ⟨src, t⟩) (fun (_, v1) => v1.term == t)) = true := by decide
-- L186 assertThat(v1.getLastAcceptedTerm(), equalTo(initialStateNode1.term()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (cs1.handleStartJoin ⟨src, t⟩)
      (fun (_, v1) => v1.lastAcceptedTerm == initialStateNode1.term)) = true := by decide
-- L187 assertThat(v1.getLastAcceptedVersion(), equalTo(initialStateNode1.version()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (cs1.handleStartJoin ⟨src, t⟩)
      (fun (_, v1) => v1.lastAcceptedVersion == initialStateNode1.version)) = true := by decide
-- L188 assertThat(cs1.getCurrentTerm(), equalTo(startJoinRequest1.getTerm()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (cs1.handleStartJoin ⟨src, t⟩) (fun (cs, _) => cs.currentTerm == t)) = true := by decide
-- L194 expectThrows(CoordinationStateRejectedException.class, () -> cs1.handleStartJoin(startJoinRequest2))
example : startJoinCases.all (fun (src, t, src2, t2) =>
    okAnd (cs1.handleStartJoin ⟨src, t⟩)
      (fun (cs, _) => isErr (cs.handleStartJoin ⟨src2, t2⟩))) = true := by decide

/-! ## testStartJoinAfterBootstrap (CoordinationStateTests.java:197)

Same draws as `startJoinCases`; `startJoinRequest3` (L221) is
`new StartJoinRequest(randomFrom(node1, node2), startJoinRequest1.getTerm())`. -/

-- L200 assertTrue(state1.getLastAcceptedConfiguration().hasQuorum(Collections.singleton(node1.getId())))
example : state1.lastAcceptedConfiguration.hasQuorum [node1.id] = true := by decide
-- L201 assertTrue(state1.getLastCommittedConfiguration().hasQuorum(Collections.singleton(node1.getId())))
example : state1.lastCommittedConfiguration.hasQuorum [node1.id] = true := by decide
-- L202 cs1.setInitialState(state1); L205 Join v1 = cs1.handleStartJoin(startJoinRequest1);
-- L206 assertThat(v1.getTargetNode(), equalTo(startJoinRequest1.getSourceNode()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (bootStartJoin src t) (fun (_, v1) => v1.targetNode == src)) = true := by decide
-- L207 assertThat(v1.getSourceNode(), equalTo(node1))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (bootStartJoin src t) (fun (_, v1) => v1.sourceNode == node1)) = true := by decide
-- L208 assertThat(v1.getTerm(), equalTo(startJoinRequest1.getTerm()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (bootStartJoin src t) (fun (_, v1) => v1.term == t)) = true := by decide
-- L209 assertThat(v1.getLastAcceptedTerm(), equalTo(state1.term()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (bootStartJoin src t) (fun (_, v1) => v1.lastAcceptedTerm == state1.term)) = true := by decide
-- L210 assertThat(v1.getLastAcceptedVersion(), equalTo(state1.version()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (bootStartJoin src t) (fun (_, v1) => v1.lastAcceptedVersion == state1.version)) = true := by decide
-- L211 assertThat(cs1.getCurrentTerm(), equalTo(startJoinRequest1.getTerm()))
example : startJoinCases.all (fun (src, t, _, _) =>
    okAnd (bootStartJoin src t) (fun (cs, _) => cs.currentTerm == t)) = true := by decide
-- L217-220 expectThrows(..., () -> cs1.handleStartJoin(startJoinRequest2)),
--          containsString("not greater than current term")
example : startJoinCases.all (fun (src, t, src2, t2) =>
    okAnd (bootStartJoin src t)
      (fun (cs, _) => rejects (cs.handleStartJoin ⟨src2, t2⟩) "not greater than current term")) = true := by decide
-- L222-225 expectThrows(..., () -> cs1.handleStartJoin(startJoinRequest3)),
--          containsString("not greater than current term")
example : startJoinCases.all (fun (src, t, src2, _) =>
    okAnd (bootStartJoin src t)
      (fun (cs, _) => rejects (cs.handleStartJoin ⟨src2, t⟩) "not greater than current term")) = true := by decide

/-! ## testJoinBeforeBootstrap (CoordinationStateTests.java:228)

`startJoinRequest1 = new StartJoinRequest(node1, randomLongBetween(1, 5))`. -/

-- L230 Join v1 = cs1.handleStartJoin(startJoinRequest1);
-- L231-234 expectThrows(..., () -> cs1.handleJoin(v1)),
--          containsString("this node has not received its initial configuration yet")
example : [1, 3, 5].all (fun t => okAnd (cs1.handleStartJoin ⟨node1, t⟩) (fun (cs, v1) =>
    rejects (cs.handleJoin ES v1) "this node has not received its initial configuration yet")) = true := by decide

/-! ## testJoinWithNoStartJoinAfterReboot (CoordinationStateTests.java:237) -/

/-- `cs1 = createCoordinationState(psr1, node1, Settings.EMPTY)` (L240): a restart over the same persisted state. -/
def reboot (cs : CS) : CS := CoordinationState.init cs.localNode cs.currentTerm cs.lastAcceptedState

-- L239 Join v1 = cs1.handleStartJoin(new StartJoinRequest(node1, randomLongBetween(1, 5))); L240 reboot;
-- L241-244 expectThrows(..., () -> cs1.handleJoin(v1)),
--          containsString("ignored join as term has not been incremented yet after reboot")
example : [1, 3, 5].all (fun t => okAnd (cs1.handleStartJoin ⟨node1, t⟩) (fun (cs, v1) =>
    rejects ((reboot cs).handleJoin ES v1)
      "ignored join as term has not been incremented yet after reboot")) = true := by decide

/-! ## testJoinWithWrongTarget (CoordinationStateTests.java:247)

L248 `assumeTrue("test only works with assertions enabled", Assertions.ENABLED)`;
L250 `Join v1 = cs1.handleStartJoin(new StartJoinRequest(node2, randomLongBetween(1, 5)))`;
L251 `expectThrows(AssertionError.class, () -> cs1.handleJoin(v1))`, `containsString("wrong node")`.

Not checked: this is the Java `assert join.targetMatches(localNode)` of `handleJoin` (CS:265), which the transcription
does not check (it is recorded in the docstring of `handleJoin`).

Supplementary check, not a Java assertion: the join targets node2, not the local node1; with assertions disabled
(production) Java goes on to reject the join because `cs1` has not been bootstrapped, and so does the transcription. -/

example : [1, 3, 5].all (fun t => okAnd (cs1.handleStartJoin ⟨node2, t⟩) (fun (cs, v1) =>
    v1.targetNode.id != cs.localNode.id &&
      rejects (cs.handleJoin ES v1) "this node has not received its initial configuration yet")) = true := by decide

/-! ## testJoinWithBadCurrentTerm (CoordinationStateTests.java:254) -/

/-- `startJoinRequest1.getTerm() = randomLongBetween(1, 5)`; `badJoin = new Join(randomFrom(node1, node2), node1,
randomLongBetween(0, startJoinRequest1.getTerm() - 1), randomNonNegativeLong(), randomNonNegativeLong())`. -/
def badCurrentTermCases : List (Nat × DiscoveryNode × Nat × Nat × Int) :=
  [(1, node1, 0, 0, 0), (5, node2, 4, 9223372036854775807, 9223372036854775807), (3, node1, 2, 17, 3)]

-- L257 cs1.setInitialState(state1); L260 cs1.handleStartJoin(new StartJoinRequest(node2, t));
-- L268-271 expectThrows(..., () -> cs1.handleJoin(badJoin)), containsString("does not match current term")
example : badCurrentTermCases.all (fun (t, src, term, lat, lav) => okAnd (bootStartJoin node2 t) (fun (cs, _) =>
    rejects (cs.handleJoin ES ⟨src, node1, term, lat, lav⟩) "does not match current term")) = true := by decide

/-! ## Joins after accepting a state of an earlier term (CoordinationStateTests.java:274-378) -/

/-- The prefix of L274-371: `cs1.setInitialState(state1)`; `cs1.handleStartJoin(new StartJoinRequest(node2, t1))`;
`cs1.handlePublishRequest(new PublishRequest(state2))` for
`state2 = clusterState(t1, v2, node1, initialConfig, initialConfig, 42L)`;
`Join v1 = cs1.handleStartJoin(new StartJoinRequest(node2, t2))`. Draws: `t1 = randomLongBetween(1, 5)`,
`v2 = randomLongBetween(2, 20)`, `t2 = randomLongBetween(t1 + 1, 10)`. -/
def acceptedThenNewTerm (t1 : Nat) (v2 : Int) (t2 : Nat) : Except String (CS × Join) := do
  let (cs, _) ← bootStartJoin node2 t1
  let (cs, _) ← cs.handlePublishRequest ⟨clusterState t1 v2 node1 initialConfig initialConfig 42⟩
  cs.handleStartJoin ⟨node2, t2⟩

/-! ### testJoinWithHigherAcceptedTerm (CoordinationStateTests.java:274) -/

/-- `(t1, v2, t2)` and `badJoin = new Join(randomFrom(node1, node2), node1, v1.getTerm(),
randomLongBetween(state2.term() + 1, 30), randomNonNegativeLong())`. -/
def higherAcceptedTermCases : List (Nat × Int × Nat × DiscoveryNode × Nat × Int) :=
  [(1, 2, 2, node1, 2, 0), (5, 20, 10, node2, 30, 9223372036854775807), (3, 7, 4, node2, 4, 5)]

-- L293-296 expectThrows(..., () -> cs1.handleJoin(badJoin)), containsString("higher than current last accepted term")
example : higherAcceptedTermCases.all (fun (t1, v2, t2, src, lat, lav) =>
    okAnd (acceptedThenNewTerm t1 v2 t2) (fun (cs, v1) =>
      rejects (cs.handleJoin ES ⟨src, node1, v1.term, lat, lav⟩)
        "higher than current last accepted term")) = true := by decide

/-! ### testJoinWithSameAcceptedTermButHigherVersion (CoordinationStateTests.java:299) -/

/-- `(t1, v2, t2)` and `badJoin = new Join(randomFrom(node1, node2), node1, v1.getTerm(), state2.term(),
randomLongBetween(state2.version() + 1, 30))`. -/
def higherVersionCases : List (Nat × Int × Nat × DiscoveryNode × Int) :=
  [(1, 2, 2, node1, 3), (5, 20, 10, node2, 30), (3, 7, 4, node1, 8)]

-- L312-315 expectThrows(..., () -> cs1.handleJoin(badJoin)),
--          containsString("higher than current last accepted version")
example : higherVersionCases.all (fun (t1, v2, t2, src, lav) =>
    okAnd (acceptedThenNewTerm t1 v2 t2) (fun (cs, v1) =>
      rejects (cs.handleJoin ES ⟨src, node1, v1.term, t1, lav⟩)
        "higher than current last accepted version")) = true := by decide

/-! ### testJoinWithLowerLastAcceptedTermWinsElection (CoordinationStateTests.java:318) -/

/-- `(t1, v2, t2)` and `join = new Join(node1, node1, v1.getTerm(), randomLongBetween(0, state2.term() - 1),
randomLongBetween(0, 20))`. -/
def lowerTermCases : List (Nat × Int × Nat × Nat × Int) :=
  [(1, 2, 2, 0, 0), (5, 20, 10, 4, 20), (3, 7, 4, 2, 15)]

/-- L330-337: the state after `cs1.handleJoin(join)`, and the results of the two `handleJoin(join)` calls. -/
def lowerTermRun (t1 : Nat) (v2 : Int) (t2 lat : Nat) (lav : Int) : Except String (CS × Bool × Bool) := do
  let (cs, v1) ← acceptedThenNewTerm t1 v2 t2
  joinTwice cs ⟨node1, node1, v1.term, lat, lav⟩

-- L331 assertTrue(cs1.handleJoin(join))
example : lowerTermCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (lowerTermRun t1 v2 t2 lat lav) (fun (_, joined, _) => joined)) = true := by decide
-- L332 assertTrue(cs1.electionWon())
example : lowerTermCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (lowerTermRun t1 v2 t2 lat lav) (fun (cs, _, _) => cs.electionWon)) = true := by decide
-- L333 assertTrue(cs1.containsJoinVoteFor(node1))
example : lowerTermCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (lowerTermRun t1 v2 t2 lat lav) (fun (cs, _, _) => cs.joinVotes.containsVoteFor node1)) = true := by decide
-- L334 assertTrue(cs1.containsJoin(join)). The transcription does not keep the `Join`s (only tests read them). Java
-- records a join exactly when `handleJoin` adds its source's vote (`addJoinVote`, CS:759-764) and drops them only in
-- `handleStartJoin`, so this holds iff `handleJoin(join)` returned true and the vote of node1 is present.
example : lowerTermCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (lowerTermRun t1 v2 t2 lat lav)
      (fun (cs, joined, _) => joined && cs.joinVotes.containsVoteFor node1)) = true := by decide
-- L335 assertFalse(cs1.containsJoinVoteFor(node2))
example : lowerTermCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (lowerTermRun t1 v2 t2 lat lav) (fun (cs, _, _) => !cs.joinVotes.containsVoteFor node2)) = true := by decide
-- L336 assertEquals(cs1.getLastPublishedVersion(), cs1.getLastAcceptedVersion())
example : lowerTermCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (lowerTermRun t1 v2 t2 lat lav)
      (fun (cs, _, _) => cs.lastPublishedVersion == cs.lastAcceptedVersion)) = true := by decide
-- L337 assertFalse(cs1.handleJoin(join))
example : lowerTermCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (lowerTermRun t1 v2 t2 lat lav) (fun (_, _, again) => !again)) = true := by decide

/-! ### testJoinWithSameLastAcceptedTermButLowerOrSameVersionWinsElection (CoordinationStateTests.java:340) -/

/-- `(t1, v2, t2)` and `join = new Join(node1, node1, v1.getTerm(), state2.term(),
randomLongBetween(0, state2.version()))`. -/
def sameTermCases : List (Nat × Int × Nat × Int) :=
  [(1, 2, 2, 0), (5, 20, 10, 20), (3, 7, 4, 7), (2, 9, 6, 4)]

/-- L352-358: the state after `cs1.handleJoin(join)`, and the results of the two `handleJoin(join)` calls. -/
def sameTermRun (t1 : Nat) (v2 : Int) (t2 : Nat) (lav : Int) : Except String (CS × Bool × Bool) := do
  let (cs, v1) ← acceptedThenNewTerm t1 v2 t2
  joinTwice cs ⟨node1, node1, v1.term, t1, lav⟩

-- L353 assertTrue(cs1.handleJoin(join))
example : sameTermCases.all (fun (t1, v2, t2, lav) =>
    okAnd (sameTermRun t1 v2 t2 lav) (fun (_, joined, _) => joined)) = true := by decide
-- L354 assertTrue(cs1.electionWon())
example : sameTermCases.all (fun (t1, v2, t2, lav) =>
    okAnd (sameTermRun t1 v2 t2 lav) (fun (cs, _, _) => cs.electionWon)) = true := by decide
-- L355 assertTrue(cs1.containsJoinVoteFor(node1))
example : sameTermCases.all (fun (t1, v2, t2, lav) =>
    okAnd (sameTermRun t1 v2 t2 lav) (fun (cs, _, _) => cs.joinVotes.containsVoteFor node1)) = true := by decide
-- L356 assertFalse(cs1.containsJoinVoteFor(node2))
example : sameTermCases.all (fun (t1, v2, t2, lav) =>
    okAnd (sameTermRun t1 v2 t2 lav) (fun (cs, _, _) => !cs.joinVotes.containsVoteFor node2)) = true := by decide
-- L357 assertEquals(cs1.getLastPublishedVersion(), cs1.getLastAcceptedVersion())
example : sameTermCases.all (fun (t1, v2, t2, lav) =>
    okAnd (sameTermRun t1 v2 t2 lav)
      (fun (cs, _, _) => cs.lastPublishedVersion == cs.lastAcceptedVersion)) = true := by decide
-- L358 assertFalse(cs1.handleJoin(join))
example : sameTermCases.all (fun (t1, v2, t2, lav) =>
    okAnd (sameTermRun t1 v2 t2 lav) (fun (_, _, again) => !again)) = true := by decide

/-! ### testJoinDoesNotWinElection (CoordinationStateTests.java:361) -/

/-- `(t1, v2, t2)` and `join = new Join(node2, node1, v1.getTerm(), randomLongBetween(0, state2.term()),
randomLongBetween(0, state2.version()))`. -/
def noWinCases : List (Nat × Int × Nat × Nat × Int) :=
  [(1, 2, 2, 0, 0), (5, 20, 10, 5, 20), (3, 7, 4, 3, 0), (4, 12, 9, 1, 12)]

/-- L373-377: the state after `cs1.handleJoin(join)`, and the results of the two `handleJoin(join)` calls. -/
def noWinRun (t1 : Nat) (v2 : Int) (t2 lat : Nat) (lav : Int) : Except String (CS × Bool × Bool) := do
  let (cs, v1) ← acceptedThenNewTerm t1 v2 t2
  joinTwice cs ⟨node2, node1, v1.term, lat, lav⟩

-- L374 assertTrue(cs1.handleJoin(join))
example : noWinCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (noWinRun t1 v2 t2 lat lav) (fun (_, joined, _) => joined)) = true := by decide
-- L375 assertFalse(cs1.electionWon())
example : noWinCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (noWinRun t1 v2 t2 lat lav) (fun (cs, _, _) => !cs.electionWon)) = true := by decide
-- L376 assertEquals(cs1.getLastPublishedVersion(), 0L)
example : noWinCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (noWinRun t1 v2 t2 lat lav) (fun (cs, _, _) => cs.lastPublishedVersion == 0)) = true := by decide
-- L377 assertFalse(cs1.handleJoin(join))
example : noWinCases.all (fun (t1, v2, t2, lat, lav) =>
    okAnd (noWinRun t1 v2 t2 lat lav) (fun (_, _, again) => !again)) = true := by decide

/-! ## Elections with differing committed and accepted configurations (CoordinationStateTests.java:380-406) -/

/-- `cs1.setInitialState(clusterState(0L, 0L, node1, committed, accepted, 42L))`;
`Join join = cs1.handleStartJoin(new StartJoinRequest(node1, randomLongBetween(1, 5)))`;
`cs1.handleJoin(join)` twice. -/
def selfJoinTwice (committed accepted : VotingConfiguration) (t : Nat) : Except String (CS × Bool × Bool) := do
  let cs ← cs1.setInitialState (clusterState 0 0 node1 committed accepted 42)
  let (cs, join) ← cs.handleStartJoin ⟨node1, t⟩
  joinTwice cs join

/-! ### testJoinDoesNotWinElectionWhenOnlyCommittedConfigQuorum (CoordinationStateTests.java:380)

`state1 = clusterState(0L, 0L, node1, configNode1, configNode2, 42L)`. -/

-- L388 assertTrue(cs1.handleJoin(join))
example : [1, 3, 5].all (fun t =>
    okAnd (selfJoinTwice configNode1 configNode2 t) (fun (_, joined, _) => joined)) = true := by decide
-- L389 assertFalse(cs1.electionWon())
example : [1, 3, 5].all (fun t =>
    okAnd (selfJoinTwice configNode1 configNode2 t) (fun (cs, _, _) => !cs.electionWon)) = true := by decide
-- L390 assertEquals(cs1.getLastPublishedVersion(), 0L)
example : [1, 3, 5].all (fun t =>
    okAnd (selfJoinTwice configNode1 configNode2 t) (fun (cs, _, _) => cs.lastPublishedVersion == 0)) = true := by
  decide
-- L391 assertFalse(cs1.handleJoin(join))
example : [1, 3, 5].all (fun t =>
    okAnd (selfJoinTwice configNode1 configNode2 t) (fun (_, _, again) => !again)) = true := by decide

/-! ### testJoinDoesNotWinElectionWhenOnlyLastAcceptedConfigQuorum (CoordinationStateTests.java:394)

`state1 = clusterState(0L, 0L, node1, configNode2, configNode1, 42L)`. -/

-- L402 assertTrue(cs1.handleJoin(join))
example : [1, 3, 5].all (fun t =>
    okAnd (selfJoinTwice configNode2 configNode1 t) (fun (_, joined, _) => joined)) = true := by decide
-- L403 assertFalse(cs1.electionWon())
example : [1, 3, 5].all (fun t =>
    okAnd (selfJoinTwice configNode2 configNode1 t) (fun (cs, _, _) => !cs.electionWon)) = true := by decide
-- L404 assertEquals(cs1.getLastPublishedVersion(), 0L)
example : [1, 3, 5].all (fun t =>
    okAnd (selfJoinTwice configNode2 configNode1 t) (fun (cs, _, _) => cs.lastPublishedVersion == 0)) = true := by
  decide
-- L405 assertFalse(cs1.handleJoin(join))
example : [1, 3, 5].all (fun t =>
    okAnd (selfJoinTwice configNode2 configNode1 t) (fun (_, _, again) => !again)) = true := by decide

/-! ## testHandleClientValue (CoordinationStateTests.java:408)

`startJoinRequest1 = new StartJoinRequest(node1, randomLongBetween(1, 5))`. `containsJoin(v)` is read as in
`testJoinWithLowerLastAcceptedTermWinsElection`: true once `handleJoin(v)` returned true; false while no vote from
`v.getSourceNode()` is present. -/

/-- `state2 = clusterState(startJoinRequest1.getTerm(), 2L, node1, initialConfig, newConfig, 42L)` with
`newConfig = VotingConfiguration.of(node2)` (L422-424). -/
def clientValueState2 (t : Nat) : State := clusterState t 2 node1 initialConfig configNode2 42

/-- What `testHandleClientValue` asserts, in order. -/
structure ClientValueObs where
  /-- L415 `cs1.handleJoin(v1)` -/
  joinedV1 : Bool
  /-- L416 `cs1.electionWon()` -/
  wonAfterV1 : Bool
  /-- L417 `cs1.containsJoin(v1)` -/
  hasV1 : Bool
  /-- L418 `cs1.containsJoin(v2)`, before `handleJoin(v2)` -/
  hasV2Before : Bool
  /-- L419 `cs1.handleJoin(v2)` -/
  joinedV2 : Bool
  /-- L420 `cs1.containsJoin(v2)` -/
  hasV2 : Bool
  /-- L426 `publishRequest.getAcceptedState()` -/
  published : State
  /-- L427 `cs1.getLastPublishedVersion()` -/
  lastPublished : Int
  /-- L430 `cs1.handleJoin(v3)` -/
  joinedV3 : Bool
  /-- L431 `cs1.getLastPublishedVersion()` -/
  lastPublishedAfterV3 : Int

def handleClientValueRun (t : Nat) : Except String ClientValueObs := do
  let (cs, v1) ← bootStartJoin node1 t
  let (_, v2) ← cs2.handleStartJoin ⟨node1, t⟩
  let (cs, joinedV1) ← cs.handleJoin ES v1
  let wonAfterV1 := cs.electionWon
  let hasV1 := joinedV1 && cs.joinVotes.containsVoteFor v1.sourceNode
  let hasV2Before := cs.joinVotes.containsVoteFor v2.sourceNode
  let (cs, joinedV2) ← cs.handleJoin ES v2
  let hasV2 := joinedV2 && cs.joinVotes.containsVoteFor v2.sourceNode
  let (cs, publishRequest) ← cs.handleClientValue (clientValueState2 t)
  let lastPublished := cs.lastPublishedVersion
  let (_, v3) ← cs3.handleStartJoin ⟨node1, t⟩
  let (cs, joinedV3) ← cs.handleJoin ES v3
  return { joinedV1, wonAfterV1, hasV1, hasV2Before, joinedV2, hasV2, published := publishRequest.acceptedState,
           lastPublished, joinedV3, lastPublishedAfterV3 := cs.lastPublishedVersion }

-- L415 assertTrue(cs1.handleJoin(v1))
example : [1, 3, 5].all (fun t => okAnd (handleClientValueRun t) (fun o => o.joinedV1)) = true := by decide
-- L416 assertTrue(cs1.electionWon())
example : [1, 3, 5].all (fun t => okAnd (handleClientValueRun t) (fun o => o.wonAfterV1)) = true := by decide
-- L417 assertTrue(cs1.containsJoin(v1))
example : [1, 3, 5].all (fun t => okAnd (handleClientValueRun t) (fun o => o.hasV1)) = true := by decide
-- L418 assertFalse(cs1.containsJoin(v2))
example : [1, 3, 5].all (fun t => okAnd (handleClientValueRun t) (fun o => !o.hasV2Before)) = true := by decide
-- L419 assertTrue(cs1.handleJoin(v2))
example : [1, 3, 5].all (fun t => okAnd (handleClientValueRun t) (fun o => o.joinedV2)) = true := by decide
-- L420 assertTrue(cs1.containsJoin(v2))
example : [1, 3, 5].all (fun t => okAnd (handleClientValueRun t) (fun o => o.hasV2)) = true := by decide
-- L425 PublishRequest publishRequest = cs1.handleClientValue(state2);
-- L426 assertThat(publishRequest.getAcceptedState(), equalTo(state2))
example : [1, 3, 5].all (fun t =>
    okAnd (handleClientValueRun t) (fun o => o.published == clientValueState2 t)) = true := by decide
-- L427 assertThat(cs1.getLastPublishedVersion(), equalTo(state2.version()))
example : [1, 3, 5].all (fun t =>
    okAnd (handleClientValueRun t) (fun o => o.lastPublished == (clientValueState2 t).version)) = true := by decide
-- L429 Join v3 = cs3.handleStartJoin(startJoinRequest1); L430 assertTrue(cs1.handleJoin(v3))
example : [1, 3, 5].all (fun t => okAnd (handleClientValueRun t) (fun o => o.joinedV3)) = true := by decide
-- L431 assertThat(cs1.getLastPublishedVersion(), equalTo(state2.version()))
example : [1, 3, 5].all (fun t =>
    okAnd (handleClientValueRun t) (fun o => o.lastPublishedAfterV3 == (clientValueState2 t).version)) = true := by
  decide

/-! ## testHandleClientValueWhenElectionNotWon (CoordinationStateTests.java:434) -/

/-- L437-439 `if (randomBoolean()) { cs1.setInitialState(state1); }` -/
def maybeBoot (b : Bool) : Except String CS := if b then cs1.setInitialState state1 else .ok cs1

-- L440-443 expectThrows(..., () -> cs1.handleClientValue(state1)), containsString("election not won")
example : [false, true].all (fun b =>
    okAnd (maybeBoot b) (fun cs => rejects (cs.handleClientValue state1) "election not won")) = true := by decide

/-! ## testHandleClientValueDuringOngoingPublication (CoordinationStateTests.java:446)

`startJoinRequest1 = new StartJoinRequest(node1, randomLongBetween(1, 5))`. -/

-- L452 assertTrue(cs1.handleJoin(v1)); L453 assertTrue(cs1.electionWon())
example : [1, 3, 5].all wonAloneOk = true := by decide
-- L456 cs1.handleClientValue(clusterState(t, 2L, node1, initialConfig, initialConfig, 42L));
-- L459-462 expectThrows(..., () -> cs1.handleClientValue(clusterState(t, 3L, ...))),
--          containsString("cannot start publishing next value before accepting previous one")
example : [1, 3, 5].all (fun t => okAnd (wonAlone t) (fun (cs, _) =>
    okAnd (cs.handleClientValue (clusterState t 2 node1 initialConfig initialConfig 42)) (fun (cs, _) =>
      rejects (cs.handleClientValue (clusterState t 3 node1 initialConfig initialConfig 42))
        "cannot start publishing next value before accepting previous one"))) = true := by decide

/-! ## testHandleClientValueWithBadTerm (CoordinationStateTests.java:465) -/

/-- `t = randomLongBetween(3, 5)`;
`term = randomBoolean() ? randomLongBetween(t + 1, 10) : randomLongBetween(0, t - 1)`. -/
def clientBadTermCases : List (Nat × Nat) := [(3, 4), (5, 10), (3, 0), (5, 4)]

-- L471 assertTrue(cs1.handleJoin(v1)); L472 assertTrue(cs1.electionWon())
example : clientBadTermCases.all (fun (t, _) => wonAloneOk t) = true := by decide
-- L478-481 expectThrows(..., () -> cs1.handleClientValue(clusterState(term, 2L, node1, initialConfig, initialConfig,
--          42L))), containsString("does not match current term")
example : clientBadTermCases.all (fun (t, term) => okAnd (wonAlone t) (fun (cs, _) =>
    rejects (cs.handleClientValue (clusterState term 2 node1 initialConfig initialConfig 42))
      "does not match current term")) = true := by decide

/-! ## testHandleClientValueWithOldVersion (CoordinationStateTests.java:484) -/

-- L490 assertTrue(cs1.handleJoin(v1)); L491 assertTrue(cs1.electionWon())
example : [1, 3, 5].all wonAloneOk = true := by decide
-- L494-497 expectThrows(..., () -> cs1.handleClientValue(clusterState(t, 0L, node1, initialConfig, initialConfig,
--          42L))), containsString("lower or equal to last published version")
example : [1, 3, 5].all (fun t => okAnd (wonAlone t) (fun (cs, _) =>
    rejects (cs.handleClientValue (clusterState t 0 node1 initialConfig initialConfig 42))
      "lower or equal to last published version")) = true := by decide

/-! ## Reconfiguration (CoordinationStateTests.java:500-577) -/

/-- `twoJoins t`, then `publishRequest = cs1.handleClientValue(clusterState(t, 2L, node1, initialConfig, newConfig1,
42L))` with `newConfig1 = VotingConfiguration.of(node2)`, and `cs1.handlePublishRequest(publishRequest)` (L511-514,
L534-537). -/
def reconfiguringTo2 (t : Nat) : Except String CS := do
  let r ← twoJoins t
  let (cs, publishRequest) ← r.leader.handleClientValue (clusterState t 2 node1 initialConfig configNode2 42)
  let (cs, _) ← cs.handlePublishRequest publishRequest
  return cs

/-! ### testHandleClientValueWithDifferentReconfigurationWhileAlreadyReconfiguring (CoordinationStateTests.java:500) -/

-- L507 assertTrue(cs1.handleJoin(v1)); L508 assertTrue(cs1.electionWon()); L509 assertTrue(cs1.handleJoin(v2))
example : [1, 3, 5].all twoJoinsOk = true := by decide
-- L517-520 expectThrows(..., () -> cs1.handleClientValue(clusterState(t, 3L, node1, initialConfig, newConfig2, 42L))),
--          containsString("only allow reconfiguration while not already reconfiguring")
example : [1, 3, 5].all (fun t => okAnd (reconfiguringTo2 t) (fun cs =>
    rejects (cs.handleClientValue (clusterState t 3 node1 initialConfig configNode3 42))
      "only allow reconfiguration while not already reconfiguring")) = true := by decide

/-! ### testHandleClientValueWithSameReconfigurationWhileAlreadyReconfiguring (CoordinationStateTests.java:523) -/

-- L530 assertTrue(cs1.handleJoin(v1)); L531 assertTrue(cs1.electionWon()); L532 assertTrue(cs1.handleJoin(v2))
example : [1, 3, 5].all twoJoinsOk = true := by decide
-- L539 cs1.handleClientValue(clusterState(t, 3L, node1, initialConfig, newConfig1, 42L)) does not throw
example : [1, 3, 5].all (fun t => okAnd (reconfiguringTo2 t) (fun cs =>
    !isErr (cs.handleClientValue (clusterState t 3 node1 initialConfig configNode2 42)))) = true := by decide

/-! ### testHandleClientValueWithIllegalCommittedConfigurationChange (CoordinationStateTests.java:542)

L543 `assumeTrue("test only works with assertions enabled", Assertions.ENABLED)`;
L556-559 `expectThrows(AssertionError.class, () -> cs1.handleClientValue(state2))`,
`containsString("last committed configuration should not change")`, for
`state2 = clusterState(t, 2L, node1, newConfig, newConfig, 42L)`, `newConfig = VotingConfiguration.of(node2)`.

Not checked: this is the Java `assert` of CS:397-398, which the transcription states as the caller contract
`clientValueContract` and does not check in `handleClientValue`.

Supplementary check, not a Java assertion: `clientValueContract` is violated here, and the handler accepts the value
(as Java does with assertions disabled, since all the rejection checks pass). -/

-- L550 assertTrue(cs1.handleJoin(v1)); L551 assertTrue(cs1.electionWon()); L552 assertTrue(cs1.handleJoin(v2))
example : [1, 3, 5].all twoJoinsOk = true := by decide

instance (cs : CS) (s : State) : Decidable (cs.clientValueContract s) :=
  inferInstanceAs (Decidable (s.lastCommittedConfiguration = cs.lastCommittedConfiguration))

example : [1, 3, 5].all (fun t => okAnd (twoJoins t) (fun r =>
    !decide (r.leader.clientValueContract (clusterState t 2 node1 configNode2 configNode2 42)) &&
      !isErr (r.leader.handleClientValue (clusterState t 2 node1 configNode2 configNode2 42)))) = true := by decide

/-! ### testHandleClientValueWithConfigurationChangeButNoJoinQuorum (CoordinationStateTests.java:562) -/

-- L568 assertTrue(cs1.handleJoin(v1)); L569 assertTrue(cs1.electionWon())
example : [1, 3, 5].all wonAloneOk = true := by decide
-- L573-576 expectThrows(..., () -> cs1.handleClientValue(clusterState(t, 2L, node1, initialConfig, newConfig, 42L))),
--          containsString("only allow reconfiguration if joinVotes have quorum for new config")
example : [1, 3, 5].all (fun t => okAnd (wonAlone t) (fun (cs, _) =>
    rejects (cs.handleClientValue (clusterState t 2 node1 initialConfig configNode2 42))
      "only allow reconfiguration if joinVotes have quorum for new config")) = true := by decide

/-! ## Publish requests (CoordinationStateTests.java:579-664) -/

/-- L583-588: `cs1.setInitialState(state1)`; `v1 = cs1.handleStartJoin(new StartJoinRequest(node1, t))`;
`if (b) { assertTrue(cs1.handleJoin(v1)); assertTrue(cs1.electionWon()); }`: the state, and whether the assertions in
the branch hold (trivially if it is not taken). -/
def maybeWon (t : Nat) (b : Bool) : Except String (CS × Bool) := do
  let (cs, v1) ← bootStartJoin node1 t
  if b then
    let (cs, joined) ← cs.handleJoin ES v1
    return (cs, joined && cs.electionWon)
  else
    return (cs, true)

/-! ### testHandlePublishRequest (CoordinationStateTests.java:579) -/

/-- `t = randomLongBetween(1, 5)`, `randomBoolean()`, `state2.version = randomLongBetween(1, 10)`,
`state3.version = randomLongBetween(state2.getVersion() + 1, 20)`. -/
def publishRequestCases : List (Nat × Bool × Int × Int) :=
  [(1, true, 1, 2), (5, false, 10, 20), (3, true, 6, 7), (2, false, 4, 15)]

/-- `clusterState(t, v, node1, initialConfig, initialConfig, 13L)` (L589, L595-602). -/
def state13 (t : Nat) (v : Int) : State := clusterState t v node1 initialConfig initialConfig 13

/-- L590: the state after `cs1.handlePublishRequest(new PublishRequest(state2))`, the branch assertions, and the
response. -/
def publishRequestRun (t : Nat) (b : Bool) (v2 : Int) : Except String (CS × Bool × PublishResponse) := do
  let (cs, branchOk) ← maybeWon t b
  let (cs, resp) ← cs.handlePublishRequest ⟨state13 t v2⟩
  return (cs, branchOk, resp)

-- L586 assertTrue(cs1.handleJoin(v1)); L587 assertTrue(cs1.electionWon()) (when the branch is taken)
example : publishRequestCases.all (fun (t, b, v2, _) =>
    okAnd (publishRequestRun t b v2) (fun (_, branchOk, _) => branchOk)) = true := by decide
-- L591 assertThat(publishResponse.getTerm(), equalTo(state2.term()))
example : publishRequestCases.all (fun (t, b, v2, _) =>
    okAnd (publishRequestRun t b v2) (fun (_, _, resp) => resp.term == (state13 t v2).term)) = true := by decide
-- L592 assertThat(publishResponse.getVersion(), equalTo(state2.version()))
example : publishRequestCases.all (fun (t, b, v2, _) =>
    okAnd (publishRequestRun t b v2) (fun (_, _, resp) => resp.version == (state13 t v2).version)) = true := by decide
-- L593 assertThat(cs1.getLastAcceptedState(), equalTo(state2))
example : publishRequestCases.all (fun (t, b, v2, _) =>
    okAnd (publishRequestRun t b v2) (fun (cs, _, _) => cs.lastAcceptedState == state13 t v2)) = true := by decide
-- L594 assertThat(value(cs1.getLastAcceptedState()), equalTo(13L))
example : publishRequestCases.all (fun (t, b, v2, _) =>
    okAnd (publishRequestRun t b v2) (fun (cs, _, _) => cs.lastAcceptedState.value == 13)) = true := by decide
-- L603 cs1.handlePublishRequest(new PublishRequest(state3)) does not throw
example : publishRequestCases.all (fun (t, b, v2, v3) =>
    okAnd (publishRequestRun t b v2)
      (fun (cs, _, _) => !isErr (cs.handlePublishRequest ⟨state13 t v3⟩))) = true := by decide

/-! ### testHandlePublishRequestWithBadTerm (CoordinationStateTests.java:606) -/

/-- `t = randomLongBetween(1, 5)`, `randomBoolean()`,
`term = randomBoolean() ? randomLongBetween(t + 1, 10) : randomLongBetween(0, t - 1)`. -/
def publishBadTermCases : List (Nat × Bool × Nat) :=
  [(1, true, 2), (5, false, 10), (3, true, 0), (5, false, 4), (1, false, 0)]

-- L613 assertTrue(cs1.handleJoin(v1)); L614 assertTrue(cs1.electionWon()) (when the branch is taken)
example : publishBadTermCases.all (fun (t, b, _) =>
    okAnd (maybeWon t b) (fun (_, branchOk) => branchOk)) = true := by decide
-- L620-623 expectThrows(..., () -> cs1.handlePublishRequest(new PublishRequest(clusterState(term, 2L, node1,
--          initialConfig, initialConfig, 42L)))), containsString("does not match current term")
example : publishBadTermCases.all (fun (t, b, term) => okAnd (maybeWon t b) (fun (cs, _) =>
    rejects (cs.handlePublishRequest ⟨clusterState term 2 node1 initialConfig initialConfig 42⟩)
      "does not match current term")) = true := by decide

/-! ### testHandlePublishRequestWithSameTermButOlderOrSameVersion (CoordinationStateTests.java:627) -/

/-- `t = randomLongBetween(1, 5)`, `randomBoolean()`, `state2.version = randomLongBetween(2, 10)`,
`state3.version = randomLongBetween(0, state2.version())`. -/
def olderVersionCases : List (Nat × Bool × Int × Int) :=
  [(1, true, 2, 0), (5, false, 10, 10), (3, true, 5, 3), (2, false, 7, 7)]

-- L634 assertTrue(cs1.handleJoin(v1)); L635 assertTrue(cs1.electionWon()) (when the branch is taken)
example : olderVersionCases.all (fun (t, b, _, _) =>
    okAnd (maybeWon t b) (fun (_, branchOk) => branchOk)) = true := by decide
-- L638 cs1.handlePublishRequest(new PublishRequest(state2));
-- L647-650 expectThrows(..., () -> cs1.handlePublishRequest(new PublishRequest(state3))),
--          containsString("lower or equal to current version")
example : olderVersionCases.all (fun (t, b, v2, v3) => okAnd (maybeWon t b) (fun (cs, _) =>
    okAnd (cs.handlePublishRequest ⟨clusterState t v2 node1 initialConfig initialConfig 42⟩) (fun (cs, _) =>
      rejects (cs.handlePublishRequest ⟨clusterState t v3 node1 initialConfig initialConfig 42⟩)
        "lower or equal to current version"))) = true := by decide

/-! ### testHandlePublishRequestWithTermHigherThanLastAcceptedTerm (CoordinationStateTests.java:654) -/

/-- `t1 = randomLongBetween(1, 5)`, the version of (the test's local) `state1` `randomLongBetween(2, 10)`,
`t2 = randomLongBetween(t1 + 1, 10)`, `state2.version = randomLongBetween(0, 20)`. -/
def higherTermCases : List (Nat × Int × Nat × Int) :=
  [(1, 2, 2, 0), (5, 10, 10, 20), (3, 7, 4, 7), (2, 9, 3, 1)]

/-- L658-663 on `cs2` (never bootstrapped): `handleStartJoin(new StartJoinRequest(node1, t1))`,
`handlePublishRequest(clusterState(t1, v1, node1, initialConfig, initialConfig, 42L))`,
`handleStartJoin(new StartJoinRequest(node1, t2))`,
`handlePublishRequest(clusterState(t2, v2, node1, initialConfig, initialConfig, 42L))`. -/
def higherTermRun (t1 : Nat) (v1 : Int) (t2 : Nat) (v2 : Int) : Except String (CS × PublishResponse) := do
  let (cs, _) ← cs2.handleStartJoin ⟨node1, t1⟩
  let (cs, _) ← cs.handlePublishRequest ⟨clusterState t1 v1 node1 initialConfig initialConfig 42⟩
  let (cs, _) ← cs.handleStartJoin ⟨node1, t2⟩
  cs.handlePublishRequest ⟨clusterState t2 v2 node1 initialConfig initialConfig 42⟩

-- L658-663: none of these calls throws
example : higherTermCases.all (fun (t1, v1, t2, v2) => !isErr (higherTermRun t1 v1 t2 v2)) = true := by decide

/-! ## Publish responses (CoordinationStateTests.java:666-796) -/

/-! ### testHandlePublishResponseWithCommit (CoordinationStateTests.java:666) -/

/-- L677 `applyCommit = cs1.handlePublishResponse(node1, publishResponse)` after `publishedOwn t 42`. -/
def withCommitRun (t : Nat) : Except String (Option ApplyCommitRequest) := do
  let (cs, publishResponse) ← publishedOwn t 42
  let (_, applyCommit) ← cs.handlePublishResponse node1 publishResponse
  return applyCommit

-- L672 assertTrue(cs1.handleJoin(v1)); L673 assertTrue(cs1.electionWon())
example : [1, 3, 5].all wonAloneOk = true := by decide
-- L678 assertTrue(applyCommit.isPresent())
example : [1, 3, 5].all (fun t => okAnd (withCommitRun t) (fun ac => ac.isSome)) = true := by decide
-- L679 assertThat(applyCommit.get().getSourceNode(), equalTo(node1))
example : [1, 3, 5].all (fun t =>
    okAnd (withCommitRun t) (fun ac => ac.map (·.sourceNode) == some node1)) = true := by decide
-- L680 assertThat(applyCommit.get().getTerm(), equalTo(state2.term()))
example : [1, 3, 5].all (fun t => okAnd (withCommitRun t) (fun ac => ac.map (·.term) == some t)) = true := by decide
-- L681 assertThat(applyCommit.get().getVersion(), equalTo(state2.version()))
example : [1, 3, 5].all (fun t => okAnd (withCommitRun t) (fun ac => ac.map (·.version) == some 2)) = true := by decide

/-! ### testHandlePublishResponseWhenSteppedDownAsLeader (CoordinationStateTests.java:684) -/

/-- `t = randomLongBetween(1, 5)`, `t2 = randomLongBetween(t + 1, 10)`, `randomFrom(node1, node2, node3)`. -/
def steppedDownCases : List (Nat × Nat × DiscoveryNode) := [(1, 2, node1), (5, 10, node2), (3, 4, node3)]

-- L690 assertTrue(cs1.handleJoin(v1)); L691 assertTrue(cs1.electionWon())
example : steppedDownCases.all (fun (t, _, _) => wonAloneOk t) = true := by decide
-- L696 cs1.handleStartJoin(new StartJoinRequest(node1, t2));
-- L697-703 expectThrows(..., () -> cs1.handlePublishResponse(randomFrom(node1, node2, node3), publishResponse)),
--          containsString("election not won")
example : steppedDownCases.all (fun (t, t2, n) => okAnd (publishedOwn t 42) (fun (cs, resp) =>
    okAnd (cs.handleStartJoin ⟨node1, t2⟩) (fun (cs, _) =>
      rejects (cs.handlePublishResponse n resp) "election not won"))) = true := by decide

/-! ### testHandlePublishResponseWithoutPublishConfigQuorum (CoordinationStateTests.java:706)

Here `state1 = clusterState(0L, 0L, node1, configNode1, configNode1, 42L)`, which is the global `state1`. -/

/-- `twoJoins t`, then `publishRequest = cs1.handleClientValue(clusterState(t, 2L, node1, configNode1, configNode2,
42L))` (L717-718, L735-736). -/
def reconfigRequest (t : Nat) : Except String (TwoJoins × CS × PublishRequest Nat) := do
  let r ← twoJoins t
  let (cs, publishRequest) ← r.leader.handleClientValue (clusterState t 2 node1 configNode1 configNode2 42)
  return (r, cs, publishRequest)

-- L713 assertTrue(cs1.handleJoin(v1)); L714 assertTrue(cs1.electionWon()); L716 assertTrue(cs1.handleJoin(v2))
example : [1, 3, 5].all twoJoinsOk = true := by decide
-- L719 publishResponse = cs1.handlePublishRequest(publishRequest);
-- L720 applyCommit = cs1.handlePublishResponse(node1, publishResponse); L721 assertFalse(applyCommit.isPresent())
example : [1, 3, 5].all (fun t => okAnd (reconfigRequest t) (fun (_, cs, publishRequest) =>
    okAnd (cs.handlePublishRequest publishRequest) (fun (cs, resp) =>
      okAnd (cs.handlePublishResponse node1 resp) (fun (_, ac) => ac.isNone)))) = true := by decide

/-! ### testHandlePublishResponseWithoutCommitedConfigQuorum (CoordinationStateTests.java:724) -/

-- L731 assertTrue(cs1.handleJoin(v1)); L732 assertTrue(cs1.electionWon()); L734 assertTrue(cs1.handleJoin(v2))
example : [1, 3, 5].all twoJoinsOk = true := by decide
-- L737 publishResponse = cs2.handlePublishRequest(publishRequest);
-- L738 applyCommit = cs1.handlePublishResponse(node2, publishResponse); L739 assertFalse(applyCommit.isPresent())
example : [1, 3, 5].all (fun t => okAnd (reconfigRequest t) (fun (r, cs, publishRequest) =>
    okAnd (r.follower.handlePublishRequest publishRequest) (fun (_, resp) =>
      okAnd (cs.handlePublishResponse node2 resp) (fun (_, ac) => ac.isNone)))) = true := by decide

/-! ### testHandlePublishResponseWithoutCommit (CoordinationStateTests.java:742) -/

-- L748 assertTrue(cs1.handleJoin(v1)); L749 assertTrue(cs1.electionWon())
example : [1, 3, 5].all wonAloneOk = true := by decide
-- L753 applyCommit = cs1.handlePublishResponse(node2, publishResponse); L754 assertFalse(applyCommit.isPresent())
example : [1, 3, 5].all (fun t => okAnd (publishedOwn t 42) (fun (cs, resp) =>
    okAnd (cs.handlePublishResponse node2 resp) (fun (_, ac) => ac.isNone))) = true := by decide

/-! ### testHandlePublishResponseWithBadTerm (CoordinationStateTests.java:757) -/

/-- `t = randomLongBetween(1, 5)`, `state2.version = randomLongBetween(2, 10)`,
`term = randomBoolean() ? randomLongBetween(t + 1, 10) : randomLongBetween(0, t - 1)`,
`randomFrom(node1, node2, node3)`. -/
def responseBadTermCases : List (Nat × Int × Nat × DiscoveryNode) :=
  [(1, 2, 2, node1), (5, 10, 0, node2), (3, 6, 10, node3), (5, 4, 4, node1)]

-- L763 assertTrue(cs1.handleJoin(v1)); L764 assertTrue(cs1.electionWon())
example : responseBadTermCases.all (fun (t, _, _, _) => wonAloneOk t) = true := by decide
-- L766 publishResponse = cs1.handlePublishRequest(new PublishRequest(state2));
-- L770-776 expectThrows(..., () -> cs1.handlePublishResponse(randomFrom(node1, node2, node3),
--          new PublishResponse(term, publishResponse.getVersion()))), containsString("does not match current term")
example : responseBadTermCases.all (fun (t, v2, term, n) => okAnd (wonAlone t) (fun (cs, _) =>
    okAnd (cs.handlePublishRequest ⟨clusterState t v2 node1 initialConfig initialConfig 42⟩) (fun (cs, resp) =>
      rejects (cs.handlePublishResponse n ⟨term, resp.version⟩) "does not match current term"))) = true := by decide

/-! ### testHandlePublishResponseWithVersionMismatch (CoordinationStateTests.java:779) -/

/-- `t = randomLongBetween(1, 5)`, `state2.version = randomLongBetween(2, 10)`, `randomFrom(node1, node2, node3)`. -/
def versionMismatchCases : List (Nat × Int × DiscoveryNode) := [(1, 2, node1), (5, 10, node2), (3, 6, node3)]

-- L785 assertTrue(cs1.handleJoin(v1)); L786 assertTrue(cs1.electionWon())
example : versionMismatchCases.all (fun (t, _, _) => wonAloneOk t) = true := by decide
-- L788 publishResponse = cs1.handlePublishRequest(new PublishRequest(state2));
-- L789-795 expectThrows(..., () -> cs1.handlePublishResponse(randomFrom(node1, node2, node3), publishResponse)),
--          containsString("does not match current version")
example : versionMismatchCases.all (fun (t, v2, n) => okAnd (wonAlone t) (fun (cs, _) =>
    okAnd (cs.handlePublishRequest ⟨clusterState t v2 node1 initialConfig initialConfig 42⟩) (fun (cs, resp) =>
      rejects (cs.handlePublishResponse n resp) "does not match current version"))) = true := by decide

/-! ## Commits (CoordinationStateTests.java:798-877) -/

/-! ### testHandleCommit (CoordinationStateTests.java:798) -/

/-- L808-813: `twoJoins t`; `publishRequest = cs1.handleClientValue(clusterState(t, 2L, node1, initialConfig, newConfig,
7L))` with `newConfig = VotingConfiguration.of(node2)`; `publishResponse = cs1.handlePublishRequest(publishRequest)`;
`cs1.handlePublishResponse(node1, publishResponse)`; `applyCommit = cs1.handlePublishResponse(node2, publishResponse)`:
the state and `applyCommit`. -/
def handleCommitRun (t : Nat) : Except String (CS × Option ApplyCommitRequest) := do
  let r ← twoJoins t
  let (cs, publishRequest) ← r.leader.handleClientValue (clusterState t 2 node1 initialConfig configNode2 7)
  let (cs, publishResponse) ← cs.handlePublishRequest publishRequest
  let (cs, _) ← cs.handlePublishResponse node1 publishResponse
  cs.handlePublishResponse node2 publishResponse

/-- L816 `cs1.handleCommit(applyCommit.get())` (a missing `applyCommit` is a rejection, as `Optional.get()` throws). -/
def commitRun (t : Nat) : Except String CS := do
  let (cs, applyCommit) ← handleCommitRun t
  match applyCommit with
  | some c => cs.handleCommit c
  | none => .error "NoSuchElementException"

-- L804 assertTrue(cs1.handleJoin(v1)); L805 assertTrue(cs1.electionWon()); L807 assertTrue(cs1.handleJoin(v2))
example : [1, 3, 5].all twoJoinsOk = true := by decide
-- L814 assertTrue(applyCommit.isPresent())
example : [1, 3, 5].all (fun t => okAnd (handleCommitRun t) (fun (_, ac) => ac.isSome)) = true := by decide
-- L815 assertThat(cs1.getLastCommittedConfiguration(), equalTo(initialConfig))
example : [1, 3, 5].all (fun t =>
    okAnd (handleCommitRun t) (fun (cs, _) => cs.lastCommittedConfiguration == initialConfig)) = true := by decide
-- L816 cs1.handleCommit(applyCommit.get()); L817 assertThat(cs1.getLastCommittedConfiguration(), equalTo(newConfig))
example : [1, 3, 5].all (fun t =>
    okAnd (commitRun t) (fun cs => cs.lastCommittedConfiguration == configNode2)) = true := by decide

/-! ### testHandleCommitWithBadCurrentTerm (CoordinationStateTests.java:820) -/

/-- `t = randomLongBetween(1, 5)`,
`term = randomBoolean() ? randomLongBetween(t + 1, 10) : randomLongBetween(0, t - 1)`. -/
def commitBadTermCases : List (Nat × Nat) := [(1, 2), (5, 0), (3, 10), (5, 4)]

-- L826 assertTrue(cs1.handleJoin(v1)); L827 assertTrue(cs1.electionWon())
example : commitBadTermCases.all (fun (t, _) => wonAloneOk t) = true := by decide
-- L831 cs1.handlePublishResponse(node1, publishResponse);
-- L835-839 expectThrows(..., () -> cs1.handleCommit(new ApplyCommitRequest(node1, term, 2L))),
--          containsString("does not match current term")
example : commitBadTermCases.all (fun (t, term) => okAnd (publishedOwn t 7) (fun (cs, resp) =>
    okAnd (cs.handlePublishResponse node1 resp) (fun (cs, _) =>
      rejects (cs.handleCommit ⟨node1, term, 2⟩) "does not match current term"))) = true := by decide

/-! ### testHandleCommitWithBadLastAcceptedTerm (CoordinationStateTests.java:842) -/

-- L848 assertTrue(cs1.handleJoin(v1)); L849 assertTrue(cs1.electionWon())
example : [1, 3, 5].all wonAloneOk = true := by decide
-- L850-856 expectThrows(..., () -> cs1.handleCommit(new ApplyCommitRequest(node1, startJoinRequest1.getTerm(), 2L))),
--          containsString("does not match last accepted term")
example : [1, 3, 5].all (fun t => okAnd (wonAlone t) (fun (cs, _) =>
    rejects (cs.handleCommit ⟨node1, t, 2⟩) "does not match last accepted term")) = true := by decide

/-! ### testHandleCommitWithBadVersion (CoordinationStateTests.java:859) -/

/-- `t = randomLongBetween(1, 5)`, the commit's version `randomLongBetween(3, 10)`. -/
def commitBadVersionCases : List (Nat × Int) := [(1, 3), (5, 10), (3, 7)]

-- L865 assertTrue(cs1.handleJoin(v1)); L866 assertTrue(cs1.electionWon())
example : commitBadVersionCases.all (fun (t, _) => wonAloneOk t) = true := by decide
-- L868 publishRequest = cs1.handleClientValue(state2); L869 cs1.handlePublishRequest(publishRequest);
-- L870-876 expectThrows(..., () -> cs1.handleCommit(new ApplyCommitRequest(node1, t, randomLongBetween(3, 10)))),
--          containsString("does not match current version")
example : commitBadVersionCases.all (fun (t, v) => okAnd (publishedOwn t 7) (fun (cs, _) =>
    rejects (cs.handleCommit ⟨node1, t, v⟩) "does not match current version")) = true := by decide

/-! ## testVoteCollection (CoordinationStateTests.java:879) -/

/-- `new DiscoveryNode("cluster-manager-ineligible", buildNewFakeTransportAddress(), emptyMap(), emptySet(), ...)`:
no roles. -/
def ineligible : DiscoveryNode := ⟨99, false⟩

/-- L880 `new VoteCollection()`, then L884 `addVote(cluster-manager-ineligible)`. -/
def vcIneligible : VoteCollection × Bool := VoteCollection.empty.addVote ineligible
/-- L890 `voteCollection.addVote(node1)` -/
def vc1 : VoteCollection := (vcIneligible.1.addVote node1).1
/-- L895 `voteCollection.addVote(node2)` -/
def vc12 : VoteCollection := (vc1.addVote node2).1

-- L881 assertTrue(voteCollection.isEmpty())
example : VoteCollection.empty.isEmpty = true := by decide
-- L883-887 assertFalse(voteCollection.addVote(new DiscoveryNode("cluster-manager-ineligible", ...)))
example : vcIneligible.2 = false := by decide
-- L888 assertTrue(voteCollection.isEmpty())
example : vcIneligible.1.isEmpty = true := by decide
-- L891 assertFalse(voteCollection.isEmpty())
example : vc1.isEmpty = false := by decide
-- L892 assertTrue(voteCollection.containsVoteFor(node1))
example : vc1.containsVoteFor node1 = true := by decide
-- L893 assertFalse(voteCollection.containsVoteFor(node2))
example : vc1.containsVoteFor node2 = false := by decide
-- L894 assertFalse(voteCollection.containsVoteFor(node3))
example : vc1.containsVoteFor node3 = false := by decide
-- L896 assertTrue(voteCollection.containsVoteFor(node1))
example : vc12.containsVoteFor node1 = true := by decide
-- L897 assertTrue(voteCollection.containsVoteFor(node2))
example : vc12.containsVoteFor node2 = true := by decide
-- L898 assertFalse(voteCollection.containsVoteFor(node3))
example : vc12.containsVoteFor node3 = false := by decide
-- L899 assertTrue(voteCollection.isQuorum(VotingConfiguration.of(node1, node2)))
example : vc12.isQuorum (cfg [1, 2]) = true := by decide
-- L900 assertTrue(voteCollection.isQuorum(VotingConfiguration.of(node1)))
example : vc12.isQuorum (cfg [1]) = true := by decide
-- L901 assertFalse(voteCollection.isQuorum(VotingConfiguration.of(node3)))
example : vc12.isQuorum (cfg [3]) = false := by decide

/-! ### L903-914 `EqualsHashCodeTestUtils.checkEqualsAndHashCode(voteCollection, copyFunction, mutationFunction)`

`copyFunction` re-adds the votes of `vc.nodes()` to a new collection, in iteration order (every node in a vote
collection is cluster-manager-eligible, so the transcription's ids are re-added as `⟨id, true⟩`); `mutationFunction`
copies and adds the vote of a new node with a random id (`7`). `checkEqualsAndHashCode` asserts that `original` equals
itself, its copy and the copy of its copy (both ways), and differs from the mutation; the `hashCode`, `null` and
foreign-type assertions have no counterpart here.

Java's `VoteCollection.equals` compares the maps of voters (by node id) and the sets of joins (empty here, as `addVote`
records none). The transcription's `=` on `VoteCollection` (its derived `DecidableEq`) is list equality, which also
compares the order of the votes. -/

/-- `copyFunction` (L903-909). -/
def copyVC (vc : VoteCollection) : VoteCollection :=
  vc.nodes.foldl (fun acc id => (acc.addVote ⟨id, true⟩).1) VoteCollection.empty

/-- `mutationFunction` (L910-914). -/
def mutateVC (vc : VoteCollection) : VoteCollection := ((copyVC vc).addVote ⟨7, true⟩).1

/-- Java's `VoteCollection.equals` on the ids the transcription keeps: the same set of voters. -/
def sameVoters (a b : VoteCollection) : Bool := a.nodes.all b.nodes.contains && b.nodes.all a.nodes.contains

-- With Java's equality on voters:
-- original.equals(original)
example : sameVoters vc12 vc12 = true := by decide
-- mutation not(equalTo(original))
example : sameVoters (mutateVC vc12) vc12 = false := by decide
-- copy.equals(copy), original.equals(copy), copy.equals(original)
example : (sameVoters (copyVC vc12) (copyVC vc12) && sameVoters vc12 (copyVC vc12) &&
    sameVoters (copyVC vc12) vc12) = true := by decide
-- secondCopy.equals(secondCopy), copy.equals(secondCopy), original.equals(secondCopy), secondCopy.equals(copy),
-- secondCopy.equals(original)
example : (sameVoters (copyVC (copyVC vc12)) (copyVC (copyVC vc12)) &&
    sameVoters (copyVC vc12) (copyVC (copyVC vc12)) && sameVoters vc12 (copyVC (copyVC vc12)) &&
    sameVoters (copyVC (copyVC vc12)) (copyVC vc12) && sameVoters (copyVC (copyVC vc12)) vc12) = true := by decide

-- With the transcription's `=`:
-- original.equals(original)
example : decide (vc12 = vc12) = true := by decide
-- mutation not(equalTo(original))
example : decide (mutateVC vc12 = vc12) = false := by decide
-- copy.equals(copy), secondCopy.equals(secondCopy), original.equals(secondCopy), secondCopy.equals(original) (the
-- second copy restores the original order: each copy reverses it)
example : (decide (copyVC vc12 = copyVC vc12) && decide (copyVC (copyVC vc12) = copyVC (copyVC vc12)) &&
    decide (vc12 = copyVC (copyVC vc12)) && decide (copyVC (copyVC vc12) = vc12)) = true := by decide
-- DISCREPANCY (no handler compares vote collections): `original.equals(copy)` fails with the transcription's `=`.
-- `vc12.nodes` is `[2, 1]` (`addVote` prepends), and re-adding the votes in that order gives
-- `copyVC vc12 = ⟨[1, 2]⟩`, so `decide (vc12 = copyVC vc12)` is `false`, while Java's map equality holds whatever the
-- order (`sameVoters` above).
-- `copy.equals(original)`, `copy.equals(secondCopy)` and `secondCopy.equals(copy)` fail the same way.
-- example : decide (vc12 = copyVC vc12) = true := by decide
-- example : decide (copyVC vc12 = vc12) = true := by decide
-- example : decide (copyVC vc12 = copyVC (copyVC vc12)) = true := by decide
-- example : decide (copyVC (copyVC vc12) = copyVC vc12) = true := by decide
-- What the transcription gives instead:
example : (decide (vc12 = copyVC vc12) || decide (copyVC vc12 = vc12) || decide (copyVC vc12 = copyVC (copyVC vc12)) ||
    decide (copyVC (copyVC vc12) = copyVC vc12)) = false := by decide

/-! ## testVotingConfiguration (CoordinationMetadataTests.java:62)

Node ids `"id1"`, ..., `"id5"` are `1`, ..., `5`; `CoordinationMetadataTests.java` lines are cited as `M<line>`. -/

/-- M63 `config0 = new VotingConfiguration(Sets.newHashSet())` -/
def config0 : VotingConfiguration := cfg []
/-- M70 `config1 = new VotingConfiguration(Sets.newHashSet("id1"))` -/
def config1 : VotingConfiguration := cfg [1]
/-- M78 `config2 = new VotingConfiguration(Sets.newHashSet("id1", "id2"))` -/
def config2 : VotingConfiguration := cfg [1, 2]
/-- M89 `config3 = new VotingConfiguration(Sets.newHashSet("id1", "id2", "id3"))` -/
def config3 : VotingConfiguration := cfg [1, 2, 3]

-- M64 assertThat(config0, equalTo(VotingConfiguration.EMPTY_CONFIG))
example : decide (config0 = VotingConfiguration.EMPTY_CONFIG) = true := by decide
-- M65 assertThat(config0.getNodeIds(), equalTo(Sets.newHashSet()))
example : (config0.nodeIds == []) = true := by decide
-- M66 assertThat(config0.isEmpty(), equalTo(true))
example : config0.isEmpty = true := by decide
-- M67 assertThat(config0.hasQuorum(Sets.newHashSet()), equalTo(false))
example : config0.hasQuorum [] = false := by decide
-- M68 assertThat(config0.hasQuorum(Sets.newHashSet("id1")), equalTo(false))
example : config0.hasQuorum [1] = false := by decide

-- M71 assertThat(config1.getNodeIds(), equalTo(Sets.newHashSet("id1")))
example : (config1.nodeIds == [1]) = true := by decide
-- M72 assertThat(config1.isEmpty(), equalTo(false))
example : config1.isEmpty = false := by decide
-- M73 assertThat(config1.hasQuorum(Sets.newHashSet("id1")), equalTo(true))
example : config1.hasQuorum [1] = true := by decide
-- M74 assertThat(config1.hasQuorum(Sets.newHashSet("id1", "id2")), equalTo(true))
example : config1.hasQuorum [1, 2] = true := by decide
-- M75 assertThat(config1.hasQuorum(Sets.newHashSet("id2")), equalTo(false))
example : config1.hasQuorum [2] = false := by decide
-- M76 assertThat(config1.hasQuorum(Sets.newHashSet()), equalTo(false))
example : config1.hasQuorum [] = false := by decide

-- M79 assertThat(config2.getNodeIds(), equalTo(Sets.newHashSet("id1", "id2")))
example : (config2.nodeIds == [1, 2]) = true := by decide
-- M80 assertThat(config2.isEmpty(), equalTo(false))
example : config2.isEmpty = false := by decide
-- M81 assertThat(config2.hasQuorum(Sets.newHashSet("id1", "id2")), equalTo(true))
example : config2.hasQuorum [1, 2] = true := by decide
-- M82 assertThat(config2.hasQuorum(Sets.newHashSet("id1", "id2", "id3")), equalTo(true))
example : config2.hasQuorum [1, 2, 3] = true := by decide
-- M83 assertThat(config2.hasQuorum(Sets.newHashSet("id1")), equalTo(false))
example : config2.hasQuorum [1] = false := by decide
-- M84 assertThat(config2.hasQuorum(Sets.newHashSet("id2")), equalTo(false))
example : config2.hasQuorum [2] = false := by decide
-- M85 assertThat(config2.hasQuorum(Sets.newHashSet("id3")), equalTo(false))
example : config2.hasQuorum [3] = false := by decide
-- M86 assertThat(config2.hasQuorum(Sets.newHashSet("id1", "id3")), equalTo(false))
example : config2.hasQuorum [1, 3] = false := by decide
-- M87 assertThat(config2.hasQuorum(Sets.newHashSet()), equalTo(false))
example : config2.hasQuorum [] = false := by decide

-- M90 assertThat(config3.getNodeIds(), equalTo(Sets.newHashSet("id1", "id2", "id3")))
example : (config3.nodeIds == [1, 2, 3]) = true := by decide
-- M91 assertThat(config3.isEmpty(), equalTo(false))
example : config3.isEmpty = false := by decide
-- M92 assertThat(config3.hasQuorum(Sets.newHashSet("id1", "id2")), equalTo(true))
example : config3.hasQuorum [1, 2] = true := by decide
-- M93 assertThat(config3.hasQuorum(Sets.newHashSet("id2", "id3")), equalTo(true))
example : config3.hasQuorum [2, 3] = true := by decide
-- M94 assertThat(config3.hasQuorum(Sets.newHashSet("id1", "id3")), equalTo(true))
example : config3.hasQuorum [1, 3] = true := by decide
-- M95 assertThat(config3.hasQuorum(Sets.newHashSet("id1", "id2", "id3")), equalTo(true))
example : config3.hasQuorum [1, 2, 3] = true := by decide
-- M96 assertThat(config3.hasQuorum(Sets.newHashSet("id1", "id2", "id4")), equalTo(true))
example : config3.hasQuorum [1, 2, 4] = true := by decide
-- M97 assertThat(config3.hasQuorum(Sets.newHashSet("id1")), equalTo(false))
example : config3.hasQuorum [1] = false := by decide
-- M98 assertThat(config3.hasQuorum(Sets.newHashSet("id2")), equalTo(false))
example : config3.hasQuorum [2] = false := by decide
-- M99 assertThat(config3.hasQuorum(Sets.newHashSet("id3")), equalTo(false))
example : config3.hasQuorum [3] = false := by decide
-- M100 assertThat(config3.hasQuorum(Sets.newHashSet("id1", "id4")), equalTo(false))
example : config3.hasQuorum [1, 4] = false := by decide
-- M101 assertThat(config3.hasQuorum(Sets.newHashSet("id1", "id4", "id5")), equalTo(false))
example : config3.hasQuorum [1, 4, 5] = false := by decide
-- M102 assertThat(config3.hasQuorum(Sets.newHashSet()), equalTo(false))
example : config3.hasQuorum [] = false := by decide

/-! ## Java `assert`s executed by the passing tests

OpenSearch runs its tests with assertions enabled, so every `assert` that a passing test reaches held. The handlers do
not check them, but the transcription states the asserted preconditions of `setInitialState` and `handleClientValue` as
contracts; these must hold at the calls the tests make, and the commit must leave the committed configuration equal to
the accepted one (CS:572). -/

instance (cs : CS) (s : State) : Decidable (cs.initialStateContract s) :=
  inferInstanceAs (Decidable (cs.lastAcceptedTerm = 0 ∧ cs.lastCommittedConfiguration.isEmpty ∧
    cs.lastPublishedVersion = 0 ∧ cs.lastPublishedConfiguration.isEmpty ∧ cs.electionWon = false ∧
    cs.joinVotes.isEmpty ∧ cs.publishVotes.isEmpty ∧ s.term = 0 ∧ s.version = cs.lastAcceptedVersion ∧
    s.lastAcceptedConfiguration.isEmpty = false ∧ s.lastCommittedConfiguration.isEmpty = false))

-- setInitialState (CS:190-201) at the bootstraps: `state1` (most tests), and the split configurations of
-- testJoinDoesNotWinElectionWhenOnlyCommittedConfigQuorum and
-- testJoinDoesNotWinElectionWhenOnlyLastAcceptedConfigQuorum
example : decide (cs1.initialStateContract state1) = true := by decide
example : decide (cs1.initialStateContract (clusterState 0 0 node1 configNode1 configNode2 42)) = true := by decide
example : decide (cs1.initialStateContract (clusterState 0 0 node1 configNode2 configNode1 42)) = true := by decide
-- handleClientValue (CS:397-398) at the calls that pass its checks (the contract only reads the configurations):
-- * publishing without reconfiguring, after `wonAlone`: testHandleClientValueDuringOngoingPublication,
--   testHandlePublishResponse{WithCommit,WhenSteppedDownAsLeader,WithoutCommit},
--   testHandleCommitWith{BadCurrentTerm,BadVersion};
-- * starting a reconfiguration to {node2}, after `twoJoins`: testHandleClientValue,
--   testHandleClientValue{WithDifferent,WithSame}ReconfigurationWhileAlreadyReconfiguring,
--   testHandlePublishResponseWithout{Publish,Commited}ConfigQuorum, testHandleCommit;
-- * continuing it: the second call of testHandleClientValueWithSameReconfigurationWhileAlreadyReconfiguring.
example : [1, 3, 5].all (fun t => okAnd (wonAlone t) (fun (cs, _) =>
    decide (cs.clientValueContract (clusterState t 2 node1 initialConfig initialConfig 42)))) = true := by decide
example : [1, 3, 5].all (fun t => okAnd (twoJoins t) (fun r =>
    decide (r.leader.clientValueContract (clusterState t 2 node1 initialConfig configNode2 42)))) = true := by decide
example : [1, 3, 5].all (fun t => okAnd (reconfiguringTo2 t) (fun cs =>
    decide (cs.clientValueContract (clusterState t 3 node1 initialConfig configNode2 42)))) = true := by decide
-- handleCommit (CS:572) in testHandleCommit:
-- assert getLastCommittedConfiguration().equals(getLastAcceptedConfiguration())
example : [1, 3, 5].all (fun t =>
    okAnd (commitRun t) (fun cs => cs.lastCommittedConfiguration == cs.lastAcceptedConfiguration)) = true := by decide

end OpenSearchCoordinationVectors
