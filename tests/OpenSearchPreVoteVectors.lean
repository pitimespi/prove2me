import Definitions.Def_OpenSearchPreVote

/-!
# OpenSearch's `PreVoteCollectorTests` and `ElectionSchedulerFactoryTests`, replayed against the transcription

The unit tests of the pre-voting round and of the election scheduler (OpenSearch
`b2a54ba5c0defba3d1d20423e911d4bf920bab19`, `server/src/test/java/org/opensearch/cluster/coordination/`:
`PreVoteCollectorTests.java`, cited as `P<line>`, and `ElectionSchedulerFactoryTests.java`, cited as `E<line>`),
replayed with concrete values against `Definitions/Def_OpenSearchPreVote.lean`. Every Java assertion that the
transcription can observe is checked by an `example` proved by `decide`, under a comment quoting it. Java's random draws
become several concrete instances per test, including the bounds of each range (0, `Long.MAX_VALUE`,
`Long.MIN_VALUE`); each check holds for all of them.

How the `PreVoteCollectorTests` fixture (P86-183) is modelled:
* `new DiscoveryNode(id, address, version)` has the `BUILT_IN_ROLES`, which include cluster-manager: "local-node" is
  `⟨0, true⟩`, "other-node" `⟨1, true⟩`, "leader-node" `⟨2, true⟩`, "other-node-i" `⟨10 + i, true⟩`.
* The collector's state is `⟨none, localResponse⟩` after `update(getLocalPreVoteResponse(), null)` (P150), or what a
  test passes to `update`. The health supplier `() -> healthStatus` is the Boolean `healthy`.
* `startCollector(votingNodes)` (P181-183) starts a round over `makeClusterState(votingNodes)` (P169-179; its metadata
  version is 0) and requests pre-votes from every key of `responsesByNode`, `localNode` included. The request to
  `localNode` goes through `TransportService.sendLocalRequest` to the node's own handler `handlePreVoteRequest`
  (PVC:100), which may refuse; the mock transport answers for each other node with `responsesByNode.get(node)`, and not
  at all for `null` (P107-109; its `handleRemoteError` only logs, P123-125). `answers` lists the answers that reach the
  round; `deliver` hands them to `PreVotingRound.handlePreVoteResponse`, with the collector's response as the
  requester's own (`getPreVoteResponse()`, PVC:245).
* `DeterministicTaskQueue.runAllRunnableTasks` runs the runnable tasks in a random order, so the answers reach the round
  in any order: each check on a round covers every order of up to 4 answers, and for more answers the rotations of the
  answers and of their reverse (`orders`).
* `electionOccurred` (P79) records that `startElection` ran; the lambda asserts `electionOccurred == false` before
  setting it (P147-148), so a passing test runs it at most once. The checks count the calls: exactly 1 for
  `assertTrue(electionOccurred)`, 0 for `assertFalse(electionOccurred)`.
* `expectThrows(RemoteTransportException.class, ...)` whose cause is `instanceOf(C)`: the handler returns `.error m`,
  where `m` contains "unhealthy node" for `C = NodeHealthCheckFailureException` (PVC:143-147) and "already a leader"
  for `C = CoordinationStateRejectedException` (PVC:162).

How the `ElectionSchedulerFactoryTests` are modelled: a draw of the settings is a `SchedulerSettings` (milliseconds);
`random.nextLong()` (ESF:204) is any `long`. The `electionCount`-th election of `assertElectionSchedule` (E63-129) is
attempt `k = electionCount - 1` of the scheduler (`thisAttempt`, ESF:201), and its `electionDelay` is `electionDelay`
below. The task queue has no execution-delay variability by default, so a task runs exactly when it is due.

Not modelled, recorded as comments at the tests: the transport and task-queue assertions (P99-103, P165-166,
P365-375); the `updateMaxTermSeen` callback, which is `l -> {}` in the fixture (P149), so no test observes it; the
collector's `assert`s on its initialisation (PVC:137) and on closing a round once (PVC:298); the scheduling itself (E78,
E94, E127-128: the transcription has the delay of each attempt, `attemptDelay`, not the scheduler's thread-pool tasks
or its `isClosed` flag); `TimeValue` parsing and the settings' error messages (E182-236, E254-263).

Result: every replayed assertion holds; no discrepancy. One observation on the Java test itself, which the
transcription shares: `lastAcceptedTerm = randomNonNegativeLong()` (P127) is 0 with probability 2^-63 (a drawn 0 or
`Long.MIN_VALUE`). The round's state is then of term 0 (`ZEN1_BWC_TERM`), whose `getVersionOrMetadataVersion()` is its
metadata version, 0 (CLS:239-244), while the fixture's own response carries `lastAcceptedVersion`; if that is positive,
the round ignores the node's own pre-vote as fresher (PVC:233-238), and `testStartsElectionIfLocalNodeIsOnlyNode`,
`testStartsElectionIfLocalNodeIsQuorum` and `testStartsElectionIfOtherNodeIsQuorum` fail, in Java as here
(supplementary check at the first of them). The instances below with `lastAcceptedTerm = 0` use
`lastAcceptedVersion = 0`.
-/

namespace OpenSearchPreVoteVectors

open OpenSearchCoordination OpenSearchPreVote

/-! ## Helpers -/

abbrev State := ClusterState Nat
abbrev Round := PreVotingRound Nat

/-- A voting configuration from its node ids in increasing order (Java `VotingConfiguration.of(...)`). -/
def cfg (l : List Nat) (h : l.Pairwise (· < ·) := by decide) : VotingConfiguration := ⟨l, h⟩

/-- The handler rejected its input (Java: it threw). -/
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

/-- `sub` occurs in `s` (compared as UTF-8 bytes; the messages are ASCII). -/
def containsStr (s sub : String) : Bool := isInfixL sub.toByteArray.data.toList s.toByteArray.data.toList

/-- The handler rejected its input with a message containing `sub`. -/
def rejects {α : Type} (x : Except String α) (sub : String) : Bool := isErr x && containsStr (errMsg x) sub

/-- The call succeeded, and `p` holds of its result. -/
def okAnd {α : Type} (x : Except String α) (p : α → Bool) : Bool :=
  match x with
  | .ok a => p a
  | .error _ => false

/-- The handler answered `r` (`assertThat(response, equalTo(r))`). -/
def answered (x : Except String PreVoteResponse) (r : PreVoteResponse) : Bool := okAnd x (· == r)

/-- `Long.MAX_VALUE`, as a term. -/
def MAXN : Nat := 9223372036854775807
/-- `Long.MAX_VALUE`, as a version or a `long`. -/
def MAXL : Int := 9223372036854775807
/-- `Long.MIN_VALUE` -/
def MINL : Int := -9223372036854775808

/-- The lists obtained by inserting `a` at each position of `l`. -/
def insertAll {α : Type} (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertAll a l).map (b :: ·)

/-- Every order of `l`. -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => (perms l).flatMap (insertAll a)

/-- The rotations of `l`. -/
def rotations {α : Type} (l : List α) : List (List α) :=
  (List.range l.length).map (fun i => l.drop i ++ l.take i)

/-- The delivery orders checked: every order of up to 4 answers; for more, the rotations of the answers and of their
reverse (each answer comes first, and last, in some checked order). -/
def orders {α : Type} (l : List α) : List (List α) :=
  if l.length ≤ 4 then perms l else rotations l ++ rotations l.reverse

/-! ## `PreVoteCollectorTests` fixture: `createObjects` (P86-151) and the helpers (P153-183) -/

/-- `localNode = new DiscoveryNode("local-node", ...)` (P131) -/
def localNode : DiscoveryNode := ⟨0, true⟩
/-- `new DiscoveryNode("other-node", ...)` -/
def otherNode : DiscoveryNode := ⟨1, true⟩
/-- `new DiscoveryNode("leader-node", ...)` (P391, P412) -/
def leaderNode : DiscoveryNode := ⟨2, true⟩
/-- `new DiscoveryNode("other-node-" + i, ...)` (P284) -/
def otherNodeI (i : Nat) : DiscoveryNode := ⟨10 + i, true⟩

/-- The draws of `createObjects` (P127-129). -/
structure Fixture where
  /-- `currentTerm = randomLongBetween(lastAcceptedTerm, Long.MAX_VALUE)` -/
  currentTerm : Nat
  /-- `lastAcceptedTerm = randomNonNegativeLong()` -/
  lastAcceptedTerm : Nat
  /-- `lastAcceptedVersion = randomNonNegativeLong()` -/
  lastAcceptedVersion : Int

/-- `getLocalPreVoteResponse()`: `new PreVoteResponse(currentTerm, lastAcceptedTerm, lastAcceptedVersion)` (P132,
P153-155). The `newPreVoteResponse` of P286, P383, P394 and P414 has the same fields. -/
def Fixture.localResponse (fx : Fixture) : PreVoteResponse :=
  ⟨fx.currentTerm, fx.lastAcceptedTerm, fx.lastAcceptedVersion⟩

/-- The collector's state after `preVoteCollector.update(getLocalPreVoteResponse(), null)` (P150). -/
def Fixture.collector (fx : Fixture) : CollectorState := ⟨none, fx.localResponse⟩

/-- `makeClusterState(votingNodes)` (P169-179): `CoordinationStateTests.clusterState(lastAcceptedTerm,
lastAcceptedVersion, localNode, config, config, 0)`, whose metadata comes from `Metadata.builder()` (version 0) with a
random cluster UUID; `config` is `VotingConfiguration.of(votingNodes)`. -/
def makeClusterState (fx : Fixture) (config : VotingConfiguration) : State where
  term := fx.lastAcceptedTerm
  version := fx.lastAcceptedVersion
  metadataVersion := 0
  lastCommittedConfiguration := config
  lastAcceptedConfiguration := config
  clusterManagerNode := none
  clusterUUIDKnown := true
  clusterUUIDCommitted := false
  value := 0

/-- The collector uses `ElectionStrategy.DEFAULT_INSTANCE` (P149). -/
def ES : ElectionStrategy := ElectionStrategy.DEFAULT_INSTANCE

/-- Instances of the draws of P127-129: `lastAcceptedTerm ∈ {0, 1, 3, 5, Long.MAX_VALUE}`, `currentTerm` from
`lastAcceptedTerm` to `Long.MAX_VALUE`, `lastAcceptedVersion ∈ {0, 17, 123456789, Long.MAX_VALUE}`; with
`lastAcceptedTerm = 0` the version is 0 (see the module documentation). -/
def fx1 : Fixture := ⟨1, 1, 0⟩
def fx2 : Fixture := ⟨9, 5, 17⟩
def fx3 : Fixture := ⟨MAXN, MAXN, MAXL⟩
def fx4 : Fixture := ⟨MAXN, 3, 0⟩
def fx5 : Fixture := ⟨0, 0, 0⟩
def fx6 : Fixture := ⟨7, 0, 0⟩
def fx7 : Fixture := ⟨2, 1, 123456789⟩

def fixtures : List Fixture := [fx1, fx2, fx3, fx4, fx5, fx6, fx7]

/-- The answers that reach a round started by `startCollector` (P181-183), which requests pre-votes from every key of
`responsesByNode`: `localNode`'s own answer, from its handler with health `healthy` and state `st`, if it answers; then
the mocked answers of the other keys, `others` (`none` is `null`: no answer). The request is
`new PreVoteRequest(transportService.getLocalNode(), state.v2().getCurrentTerm())` (PVC:112, 184). -/
def answers (healthy : Bool) (st : CollectorState) (others : List (DiscoveryNode × Option PreVoteResponse)) :
    List (DiscoveryNode × PreVoteResponse) :=
  let own : List (DiscoveryNode × PreVoteResponse) :=
    match handlePreVoteRequest healthy st ⟨localNode, st.response.currentTerm⟩ with
    | .ok r => [(localNode, r)]
    | .error _ => []
  own ++ others.filterMap (fun p => p.2.map (fun r => (p.1, r)))

/-- The answers handled in order by `PreVotingRound.handlePreVoteResponse`, `lr` being the collector's response
(`getPreVoteResponse()`, PVC:245): the final round and the number of `startElection` calls. -/
def deliver (lr : PreVoteResponse) (r : Round) (as : List (DiscoveryNode × PreVoteResponse)) : Round × Nat :=
  as.foldl (fun acc p =>
    let res := acc.1.handlePreVoteResponse ES lr p.2 p.1
    (res.1, if res.2.1 then acc.2 + 1 else acc.2)) (r, 0)

/-- The number of `startElection` calls, for each checked order in which the answers `as` reach the round `r`. -/
def electionCalls (lr : PreVoteResponse) (r : Round) (as : List (DiscoveryNode × PreVoteResponse)) : List Nat :=
  (orders as).map (fun o => (deliver lr r o).2)

/-- The round of `startCollector(votingNodes)` (P181-183), `config` being `VotingConfiguration.of(votingNodes)`. -/
def startCollector (fx : Fixture) (config : VotingConfiguration) : Round :=
  PreVotingRound.start (makeClusterState fx config) localNode

/-- `startAndRunCollector(votingNodes)` (P157-167) with the fixture `fx`, the other keys of `responsesByNode` and their
entries `others`, and the node's health: the number of `startElection` calls, for each checked delivery order. -/
def startAndRun (healthy : Bool) (fx : Fixture) (config : VotingConfiguration)
    (others : List (DiscoveryNode × Option PreVoteResponse)) : List Nat :=
  electionCalls fx.localResponse (startCollector fx config) (answers healthy fx.collector others)

/-! Not modelled, for every test that starts a round: the mock transport's assertions on each request sent to another
node (P99 the action is `REQUEST_PRE_VOTE_ACTION_NAME`, P100 the request is a `PreVoteRequest`, P101 it is not sent to
`localNode` through the mock, P103 its source is `localNode`): the transcription does not build requests (`answers`
builds the one to `localNode` as PVC:112 and PVC:184 do); and `runCollector`'s P165
`assertFalse(deterministicTaskQueue.hasDeferredTasks())`, P166 `assertFalse(deterministicTaskQueue.hasRunnableTasks())`.
The round is closed after `runCollector` (try-with-resources, P158), which changes no outcome; PVC:298 asserts it was
not closed before, and the transcription's `close` has no such check. -/

/-! ## testStartsElectionIfLocalNodeIsOnlyNode (PreVoteCollectorTests.java:185) -/

-- P186 startAndRunCollector(localNode); P187 assertTrue(electionOccurred)
example : fixtures.all (fun fx => (startAndRun true fx (cfg [0]) []).all (· == 1)) = true := by decide

-- Supplementary, not a Java assertion: the draws `lastAcceptedTerm = 0` (probability 2^-63), `lastAcceptedVersion > 0`
-- make P187 fail, in Java as here: the round's term-0 state compares metadata versions (0), so the node's own pre-vote
-- is fresher and ignored (PVC:233-238), and no election starts.
example : [(⟨0, 0, 1⟩ : Fixture), ⟨5, 0, MAXL⟩].all (fun fx =>
    (startAndRun true fx (cfg [0]) []).all (· == 0)) = true := by decide

/-! ## testNoElectionStartIfLocalNodeIsOnlyNodeAndUnhealthy (PreVoteCollectorTests.java:190) -/

-- P191 healthStatus = new StatusInfo(UNHEALTHY, "unhealthy-info");
-- P192 preVoteCollector.update(getLocalPreVoteResponse(), null);
-- P193 startAndRunCollector(localNode); P194 assertFalse(electionOccurred)
example : fixtures.all (fun fx => (startAndRun false fx (cfg [0]) []).all (· == 0)) = true := by decide

/-! ## testStartsElectionIfLocalNodeIsQuorum (PreVoteCollectorTests.java:197)

Despite its name, the voting configuration is `{other-node}` (`startAndRunCollector(otherNode)`, P200): the test is the
same as the next one. -/

-- P199 responsesByNode.put(otherNode, getLocalPreVoteResponse()); P200 startAndRunCollector(otherNode);
-- P201 assertTrue(electionOccurred)
example : fixtures.all (fun fx =>
    (startAndRun true fx (cfg [1]) [(otherNode, some fx.localResponse)]).all (· == 1)) = true := by decide

/-! ## testStartsElectionIfOtherNodeIsQuorum (PreVoteCollectorTests.java:204) -/

-- P206 responsesByNode.put(otherNode, getLocalPreVoteResponse()); P207 startAndRunCollector(otherNode);
-- P208 assertTrue(electionOccurred)
example : fixtures.all (fun fx =>
    (startAndRun true fx (cfg [1]) [(otherNode, some fx.localResponse)]).all (· == 1)) = true := by decide

/-! ## testDoesNotStartsElectionIfOtherNodeIsQuorumAndDoesNotRespond (PreVoteCollectorTests.java:211) -/

-- P213 responsesByNode.put(otherNode, null); P214 startAndRunCollector(otherNode); P215 assertFalse(electionOccurred)
example : fixtures.all (fun fx => (startAndRun true fx (cfg [1]) [(otherNode, none)]).all (· == 0)) = true := by decide

/-! ## testUnhealthyNodeDoesNotOfferPreVote (PreVoteCollectorTests.java:218)

`handlePreVoteRequestViaTransportService(request)` (P333-377) sends the request to `localNode`, whose handler is
`handlePreVoteRequest` with the collector's state; the handler first calls `updateMaxTermSeen(request.getCurrentTerm())`
(PVC:134), a no-op here (P149) and not modelled. Not modelled either: P365
`assertFalse(deterministicTaskQueue.hasDeferredTasks())`, and P371 `assertThat(response, nullValue())` when an exception
came back (P375 `assertThat(response, not(nullValue()))` otherwise): the handler's result is either a response or a
rejection. -/

/-- `term = randomNonNegativeLong()` (P219, P380, P390, P411) -/
def requestTerms : List Nat := [0, 1, 42, MAXN]

-- P220 healthStatus = new StatusInfo(UNHEALTHY, "unhealthy-info");
-- P222-225 expectThrows(RemoteTransportException.class,
--          () -> handlePreVoteRequestViaTransportService(new PreVoteRequest(otherNode, term)));
-- P226 assertThat(remoteTransportException.getCause(), instanceOf(NodeHealthCheckFailureException.class))
example : fixtures.all (fun fx => requestTerms.all (fun t =>
    rejects (handlePreVoteRequest false fx.collector ⟨otherNode, t⟩) "unhealthy node")) = true := by decide

/-! ## testDoesNotStartElectionIfStopped (PreVoteCollectorTests.java:229)

The answers reach the round after it is closed, and are ignored before `updateMaxTermSeen` (PVC:226-229; the
transcription returns `none` for its argument). The round is closed once (PVC:298). -/

-- P231 responsesByNode.put(otherNode, getLocalPreVoteResponse()); P232 startCollector(otherNode).close();
-- P233 runCollector(); P234 assertFalse(electionOccurred)
example : fixtures.all (fun fx =>
    (electionCalls fx.localResponse (startCollector fx (cfg [1])).close
      (answers true fx.collector [(otherNode, some fx.localResponse)])).all (· == 0)) = true := by decide

/-! ## testIgnoresPreVotesFromLaterTerms (PreVoteCollectorTests.java:237) -/

/-- P238 `assumeTrue(lastAcceptedTerm < currentTerm - 1)`: the fixtures `fx2`, `fx4`, `fx6`; with the draws of P243,
`randomLongBetween(lastAcceptedTerm + 1, currentTerm - 1)` and `randomNonNegativeLong()`. -/
def laterTermCases : List (Fixture × Nat × Int) :=
  [(fx2, 6, 0), (fx2, 8, MAXL), (fx4, 4, 17), (fx4, MAXN - 1, 0), (fx6, 1, 0), (fx6, 6, 5)]

-- P241-244 responsesByNode.put(otherNode, new PreVoteResponse(currentTerm,
--          randomLongBetween(lastAcceptedTerm + 1, currentTerm - 1), randomNonNegativeLong()));
-- P245 startAndRunCollector(otherNode); P246 assertFalse(electionOccurred)
example : laterTermCases.all (fun (fx, t, v) =>
    (startAndRun true fx (cfg [1]) [(otherNode, some ⟨fx.currentTerm, t, v⟩)]).all (· == 0)) = true := by decide

/-! ## testIgnoresPreVotesFromLaterVersionInSameTerm (PreVoteCollectorTests.java:249) -/

/-- P250 `assumeTrue(lastAcceptedVersion < Long.MAX_VALUE)`: every fixture but `fx3`; with the draw of P255,
`randomLongBetween(lastAcceptedVersion + 1, Long.MAX_VALUE)`. -/
def laterVersionCases : List (Fixture × Int) :=
  [(fx1, 1), (fx1, MAXL), (fx2, 18), (fx2, MAXL), (fx4, 1), (fx5, 1), (fx5, MAXL), (fx6, 2), (fx7, 123456790)]

-- P253-256 responsesByNode.put(otherNode, new PreVoteResponse(currentTerm, lastAcceptedTerm,
--          randomLongBetween(lastAcceptedVersion + 1, Long.MAX_VALUE)));
-- P257 startAndRunCollector(otherNode); P258 assertFalse(electionOccurred)
example : laterVersionCases.all (fun (fx, v) =>
    (startAndRun true fx (cfg [1]) [(otherNode, some ⟨fx.currentTerm, fx.lastAcceptedTerm, v⟩)]).all (· == 0)) =
    true := by decide

/-! ## testAcceptsPreVotesFromAnyVersionInEarlierTerms (PreVoteCollectorTests.java:261) -/

/-- P262 `assumeTrue(0 < lastAcceptedTerm)`: the fixtures `fx1`, `fx2`, `fx3`, `fx4`, `fx7`; with the draws of P267,
`randomLongBetween(0, lastAcceptedTerm - 1)` and `randomNonNegativeLong()`. -/
def earlierTermCases : List (Fixture × Nat × Int) :=
  [(fx1, 0, 0), (fx1, 0, MAXL), (fx2, 0, 0), (fx2, 4, 18), (fx2, 4, MAXL), (fx3, 0, MAXL), (fx3, MAXN - 1, MAXL),
   (fx4, 2, 5), (fx7, 0, 999999999)]

-- P265-268 responsesByNode.put(otherNode, new PreVoteResponse(currentTerm, randomLongBetween(0, lastAcceptedTerm - 1),
--          randomNonNegativeLong()));
-- P269 startAndRunCollector(otherNode); P270 assertTrue(electionOccurred)
example : earlierTermCases.all (fun (fx, t, v) =>
    (startAndRun true fx (cfg [1]) [(otherNode, some ⟨fx.currentTerm, t, v⟩)]).all (· == 1)) = true := by decide

/-! ## testPrevotingIndicatesElectionSuccess (PreVoteCollectorTests.java:278)

P279 `assumeTrue(currentTerm < Long.MAX_VALUE)`: the fixtures `fx1`, `fx2`, `fx5`, `fx6`, `fx7`. The loop P283-291 puts
`nodeCount` other nodes into `responsesByNode`, each with `null` or `randomPreVoteResponse()` (P273-276:
`currentTerm = randomNonNegativeLong()`, `lastAcceptedTerm` from 0 to it, `lastAcceptedVersion =
randomNonNegativeLong()`), calls `preVoteCollector.update(newPreVoteResponse, null)` with the fixture's response (no
change), and draws each node into `votingNodesSet` or not. The voting configuration never contains `localNode`. -/

/-- A draw of `testPrevotingIndicatesElectionSuccess`. -/
structure PrevotingCase where
  fx : Fixture
  /-- `responsesByNode.get(other-node-i)` for `i < nodeCount` (P282, P285) -/
  others : List (Option PreVoteResponse)
  /-- `VotingConfiguration.of(votingNodes)` (P293-294): the ids `10 + i` of the nodes drawn into `votingNodesSet` -/
  config : VotingConfiguration
  /-- `newTerm = randomLongBetween(currentTerm + 1, Long.MAX_VALUE)` (P308) -/
  newTerm : Nat

/-- The entries of `responsesByNode` for "other-node-i", "other-node-(i+1)", ... -/
def entriesFrom (i : Nat) : List (Option PreVoteResponse) → List (DiscoveryNode × Option PreVoteResponse)
  | [] => []
  | o :: os => (otherNodeI i, o) :: entriesFrom (i + 1) os

/-- P294 `startAndRunCollector(votingNodes)`: the number of `startElection` calls, for each checked delivery order. -/
def PrevotingCase.elections (c : PrevotingCase) : List Nat :=
  startAndRun true c.fx c.config (entriesFrom 0 c.others)

/-- P296-310: `coordinationState`, created over
`new InMemoryPersistedState(currentTerm, makeClusterState(votingNodes))`, after
`handleStartJoin(new StartJoinRequest(localNode, newTerm))`. -/
def PrevotingCase.startJoin (c : PrevotingCase) : Except String (CoordinationState Nat × Join) :=
  (CoordinationState.init localNode c.fx.currentTerm (makeClusterState c.fx c.config)).handleStartJoin
    ⟨localNode, c.newTerm⟩

/-- P312-328: `new Join(node, localNode, newTerm, response.getLastAcceptedTerm(), response.getLastAcceptedVersion())`
for each entry of `responsesByNode` with a response, `localNode`'s included. -/
def PrevotingCase.joins (c : PrevotingCase) : List Join :=
  ((localNode, some c.fx.localResponse) :: entriesFrom 0 c.others).filterMap (fun p =>
    p.2.map (fun r => ⟨p.1, localNode, c.newTerm, r.lastAcceptedTerm, r.lastAcceptedVersion⟩))

/-- The draws. In the comments, "ok" is a response the round records, "fresher" one it ignores (PVC:233-238), "null" no
response; the outcome follows. -/
def prevotingCases : List PrevotingCase :=
  [ -- nodeCount = 0: empty configuration; no election, and the only join is rejected (no initial configuration)
    ⟨fx1, [], cfg [], 2⟩,
    -- one voter, ok (earlier term): election
    ⟨fx2, [some ⟨3, 2, 1000⟩], cfg [10], 10⟩,
    -- one voter, fresher (later term): none
    ⟨fx2, [some ⟨8, 6, 0⟩], cfg [10], MAXN⟩,
    -- one voter, null: none
    ⟨fx2, [none], cfg [10], 10⟩,
    -- one node, ok, not drawn as a voter: empty configuration, none
    ⟨fx2, [some ⟨9, 5, 17⟩], cfg [], 11⟩,
    -- voters ok / fresher (same term, later version) / null: 1 of 3, none
    ⟨fx7, [some ⟨2, 1, 0⟩, some ⟨5, 1, 123456790⟩, none], cfg [10, 11, 12], 3⟩,
    -- voters ok (equal) / ok (earlier term) / null: 2 of 3, election
    ⟨fx7, [some ⟨2, 1, 123456789⟩, some ⟨0, 0, MAXL⟩, none], cfg [10, 11, 12], MAXN⟩,
    -- voters 0, 2, 4: ok / fresher / ok; nodes 1 (null) and 3 (ok) not voters: 2 of 3, election
    ⟨fx2, [some ⟨5, 5, 17⟩, none, some ⟨MAXN, MAXN, 0⟩, some ⟨1, 0, 0⟩, some ⟨6, 4, MAXL⟩], cfg [10, 12, 14], 10⟩,
    -- term 0: voters 1 (ok) and 3 (null): 1 of 2, none
    ⟨fx6, [none, some ⟨7, 0, 0⟩, none, none, none], cfg [11, 13], 8⟩,
    -- term 0: voters fresher (term 0 compares metadata versions: 1 > 0) / ok: 1 of 2, none
    ⟨fx5, [some ⟨3, 0, 1⟩, some ⟨0, 0, 0⟩], cfg [10, 11], 1⟩,
    -- term 0: voters ok / ok: election
    ⟨fx5, [some ⟨0, 0, 0⟩, some ⟨4, 0, 0⟩], cfg [10, 11], MAXN⟩,
    -- voters ok / ok / fresher (same term, later version) / ok: 3 of 4, election
    ⟨fx1, [some ⟨1, 1, 0⟩, some ⟨1, 0, 5⟩, some ⟨1, 1, 1⟩, some ⟨MAXN, 0, 0⟩], cfg [10, 11, 12, 13], 2⟩,
    -- voters fresher (term) / fresher (version) / ok / ok: 2 of 4 is no quorum, none
    ⟨fx2, [some ⟨7, 6, 0⟩, some ⟨6, 5, 18⟩, some ⟨5, 5, 17⟩, some ⟨5, 1, 0⟩], cfg [10, 11, 12, 13], 10⟩,
    -- five voters, all ok: election
    ⟨fx2, [some ⟨9, 5, 17⟩, some ⟨9, 5, 0⟩, some ⟨3, 3, MAXL⟩, some ⟨0, 0, 0⟩, some ⟨MAXN, 4, 2⟩],
      cfg [10, 11, 12, 13, 14], MAXN⟩ ]

-- P310 coordinationState.handleStartJoin(new StartJoinRequest(localNode, newTerm)) (outside any `try`: it succeeds);
-- P312-328 the joins, in `responsesByNode`'s iteration order (here: as listed, and reversed), rejections ignored;
-- P330 assertThat(coordinationState.electionWon(), equalTo(electionOccurred))
example : prevotingCases.all (fun c => okAnd c.startJoin (fun (cs, _) =>
    [c.joins, c.joins.reverse].all (fun js =>
      let won := (handleJoins ES cs js).electionWon
      c.elections.all (fun k => (k == 1) == won)))) = true := by decide

-- P147 assert electionOccurred == false (startElection runs at most once)
example : prevotingCases.all (fun c => c.elections.all (fun k => decide (k ≤ 1))) = true := by decide

-- Supplementary, not a Java assertion: the draws cover both outcomes (electionOccurred, in the order of the list).
example : (prevotingCases.map (fun c => c.elections.all (· == 1)) ==
    [false, true, false, false, false, false, true, true, false, false, true, true, false, true]) = true := by decide

/-! ## testResponseIfCandidate (PreVoteCollectorTests.java:379) -/

-- P383-384 preVoteCollector.update(newPreVoteResponse, null);
-- P386 assertThat(handlePreVoteRequestViaTransportService(new PreVoteRequest(otherNode, term)),
--      equalTo(newPreVoteResponse))
example : fixtures.all (fun fx => requestTerms.all (fun t =>
    answered (handlePreVoteRequest true ⟨none, fx.localResponse⟩ ⟨otherNode, t⟩) fx.localResponse)) = true := by
  decide

/-! ## testResponseToNonLeaderIfNotCandidate (PreVoteCollectorTests.java:389) -/

-- P394-395 preVoteCollector.update(newPreVoteResponse, leaderNode);
-- P397-400 expectThrows(RemoteTransportException.class,
--          () -> handlePreVoteRequestViaTransportService(new PreVoteRequest(otherNode, term)));
-- P401 assertThat(remoteTransportException.getCause(), instanceOf(CoordinationStateRejectedException.class))
example : fixtures.all (fun fx => requestTerms.all (fun t =>
    rejects (handlePreVoteRequest true ⟨some leaderNode, fx.localResponse⟩ ⟨otherNode, t⟩) "already a leader")) =
    true := by decide

/-! ## testResponseToRequestFromLeader (PreVoteCollectorTests.java:404) -/

-- P414-415 preVoteCollector.update(newPreVoteResponse, leaderNode);
-- P417 assertThat(handlePreVoteRequestViaTransportService(new PreVoteRequest(leaderNode, term)),
--      equalTo(newPreVoteResponse))
example : fixtures.all (fun fx => requestTerms.all (fun t =>
    answered (handlePreVoteRequest true ⟨some leaderNode, fx.localResponse⟩ ⟨leaderNode, t⟩) fx.localResponse)) =
    true := by decide

/-! ## `ElectionSchedulerFactoryTests`: helpers -/

instance (s : SchedulerSettings) : Decidable s.Valid :=
  inferInstanceAs (Decidable (1 ≤ s.initialTimeout ∧ s.initialTimeout ≤ 10000 ∧ 1 ≤ s.backoffTime ∧
    s.backoffTime ≤ 60000 ∧ 200 ≤ s.maxTimeout ∧ s.maxTimeout ≤ 300000 ∧ s.initialTimeout ≤ s.maxTimeout ∧
    1 ≤ s.duration ∧ s.duration ≤ 300000))

/-- The settings are read without an `IllegalArgumentException`: each within its bounds (ESF:85-115), and the maximum
timeout at least the initial one (the constructor's check, ESF:133-143). -/
def valid (s : SchedulerSettings) : Bool := decide s.Valid

/-- `electionDelay` (E99, E110) of the election that is attempt `k` of the scheduler, `rn` being the drawn
`random.nextLong()`. The first is measured from the start of the scheduler (E82) and includes the initial grace period
`g` (E76-79); a later one is measured from `lastElectionFinishTime = thisElectionStartTime + duration` (E124), attempt
`k ≥ 1` being scheduled with grace period `duration` when attempt `k - 1` fires (ESF:218). -/
def electionDelay (s : SchedulerSettings) (k : Nat) (rn : Int) (g : Nat) : Int :=
  if k = 0 then attemptDelay s 0 rn g else (attemptDelay s k rn s.duration : Int) - s.duration

/-! ## testRetriesOnCorrectSchedule (ElectionSchedulerFactoryTests.java:131)

The settings drawn by E132-165: `initial_timeout` from 1 to 10000 or the default 100, `back_off_time` from 1 to 60000 or
the default 100, `max_timeout` from `max(200, initial_timeout)` to 180000 or the default 10000, `duration` from 1 to
300000 or the default 500. `assertElectionSchedule` (E63-129) is called twice (E174, E177); the second call, on a new
scheduler whose attempts are numbered from 0 again (ESF:153, 193), repeats the same assertions with a new grace period,
covered by the same checks.

Not modelled: E78 `assertTrue(electionStarted.compareAndSet(false, true))` and E94
`assertTrue(electionStarted.compareAndSet(true, false))` (the scheduler does not run the election task again before the
test has seen the previous run), and E127-128 `deterministicTaskQueue.runAllTasks(); assertFalse(electionStarted.get())`
(once closed, the scheduler starts no election, ESF:196-199, 214-215): the transcription has no scheduler state. -/

/-- The draws: all defaults; the lowest; the highest; `max_timeout` at its lowest for `initial_timeout = 10000`; three
others. -/
def schedSettings : List SchedulerSettings :=
  [SchedulerSettings.default, ⟨1, 1, 200, 1⟩, ⟨10000, 60000, 180000, 300000⟩, ⟨10000, 1, 10000, 500⟩,
   ⟨3517, 42, 77777, 1234⟩, ⟨150, 60000, 200, 299999⟩, ⟨100, 7, 10000, 300000⟩]

/-- `randomGracePeriod()`: `randomLongBetween(0, 10000)` milliseconds (E59-61, E72). -/
def gracePeriods : List Nat := [0, 1, 4321, 10000]

/-- `random.nextLong()` (ESF:204): any `long`. -/
def randomLongs : List Int :=
  [0, 1, -1, MINL, MAXL, MINL + 1, MAXL - 1, 99, 199, 9999, 179999, 6148914691236517205, -123456789012345678]

/-- Attempts `k = electionCount - 1 ≥ 1` of the later elections (E108-122). -/
def laterAttempts : List Nat := [1, 2, 3, 50, 99, 100, 999, 1000, 2999, 180000]

-- E168-172 new ElectionSchedulerFactory(settings, random(), ...) does not throw on the drawn settings
example : schedSettings.all valid = true := by decide

-- E102 assertThat(electionDelay, greaterThanOrEqualTo(initialGracePeriod.millis()))   (electionCount == 1)
example : schedSettings.all (fun s => gracePeriods.all (fun g => randomLongs.all (fun rn =>
    decide (electionDelay s 0 rn g ≥ g)))) = true := by decide
-- E105 assertThat(electionDelay, lessThanOrEqualTo(initialTimeout + initialGracePeriod.millis()))
example : schedSettings.all (fun s => gracePeriods.all (fun g => randomLongs.all (fun rn =>
    decide (electionDelay s 0 rn g ≤ s.initialTimeout + g)))) = true := by decide
-- E106 assertThat(electionDelay, lessThanOrEqualTo(maxTimeout + initialGracePeriod.millis()))
example : schedSettings.all (fun s => gracePeriods.all (fun g => randomLongs.all (fun rn =>
    decide (electionDelay s 0 rn g ≤ s.maxTimeout + g)))) = true := by decide

-- E113 assertThat(electionDelay, lessThanOrEqualTo(initialTimeout + backOffTime * (electionCount - 1)))
--      (electionCount > 1; the grace period argument is unused for k ≥ 1)
example : schedSettings.all (fun s => laterAttempts.all (fun k => randomLongs.all (fun rn =>
    decide (electionDelay s k rn 0 ≤ s.initialTimeout + s.backoffTime * k)))) = true := by decide
-- E114 assertThat(electionDelay, lessThanOrEqualTo(maxTimeout))
example : schedSettings.all (fun s => laterAttempts.all (fun k => randomLongs.all (fun rn =>
    decide (electionDelay s k rn 0 ≤ s.maxTimeout)))) = true := by decide

-- E116-121, not an assertion but the loop's only exit, which the test must reach ("Run until we get a delay close to
-- the maximum to show that backing off does work"): `electionCount >= 1000 && electionDelay >= maxTimeout * 0.99`.
-- From attempt `maxTimeout` on, the bound is `maxTimeout` (back-off ≥ 1 ms), and a draw reaches it.
example : schedSettings.all (fun s => maxDelay s (999 + s.maxTimeout) == s.maxTimeout &&
    decide (100 * electionDelay s (999 + s.maxTimeout) (s.maxTimeout - 1) 0 ≥ 99 * s.maxTimeout)) = true := by decide

-- ESF:170 assert 0 < upperBound, at every attempt (`toPositiveLongAtMost(random.nextLong(), maxDelayMillis)`, ESF:204)
example : schedSettings.all (fun s => (0 :: laterAttempts).all (fun k => decide (0 < maxDelay s k))) = true := by
  decide

-- Supplementary, not a Java assertion: the delays equal those Java computes. The table was computed by running the
-- expressions of ESF:203-204 (with ESF:158-172 verbatim) under OpenJDK 21, for attempts 0, 1, 2, 99, 100, 1000 and
-- `random.nextLong()` = 0, -1, Long.MIN_VALUE, Long.MAX_VALUE, 123456789, with grace period 0 for attempt 0 (as
-- `Coordinator.startElectionScheduler` passes, CO:1574) and `duration` for the others.
example : ([SchedulerSettings.default, ⟨1, 1, 200, 1⟩, ⟨10000, 60000, 180000, 300000⟩, ⟨3517, 42, 77777, 1234⟩].map
    (fun s => [0, 1, 2, 99, 100, 1000].map (fun k => [0, -1, MINL, MAXL, 123456789].map (fun rn =>
      attemptDelay s k rn (if k = 0 then 0 else s.duration)))) ==
    [[[1, 2, 1, 8, 90], [501, 502, 501, 508, 690], [501, 502, 501, 508, 690], [501, 502, 501, 6308, 7290],
      [501, 502, 501, 6308, 7290], [501, 502, 501, 6308, 7290]],
     [[1, 1, 1, 1, 1], [2, 3, 2, 3, 3], [2, 3, 2, 3, 2], [2, 3, 2, 9, 91], [2, 3, 2, 91, 47], [2, 3, 2, 9, 191]],
     [[1, 2, 1, 5808, 6790], [300001, 300002, 300001, 365808, 346790], [300001, 300002, 300001, 385808, 386790],
      [300001, 300002, 300001, 355808, 456790], [300001, 300002, 300001, 355808, 456790],
      [300001, 300002, 300001, 355808, 456790]],
     [[1, 2, 1, 2488, 3056], [1235, 1236, 1235, 2491, 3432], [1235, 1236, 1235, 2568, 1340],
      [1235, 1236, 1235, 3892, 5649], [1235, 1236, 1235, 8369, 1458], [1235, 1236, 1235, 12369, 15920]]]) = true := by
  decide

/-! ## testSettingsValidation (ElectionSchedulerFactoryTests.java:180)

Each block sets some keys; the others take their defaults (100, 100, 10000, 500 ms). The transcription has the bounds
(`Valid`), not the parser or its messages: each check below is that the bad value makes the settings invalid, and that
the bound named in the message is exact (the settings are valid at it). `initial_timeout = 10001ms` would also fail the
constructor's check against the default `max_timeout` (10 s); there `max_timeout` is set to 300 s, so that only the
bound of `initial_timeout` fails. -/

-- E182-184 initial_timeout "0s": IllegalArgumentException
--          "failed to parse value [0s] for setting [cluster.election.initial_timeout], must be >= [1ms]"
example : (!valid ⟨0, 100, 10000, 500⟩ && valid ⟨1, 100, 10000, 500⟩) = true := by decide
-- E188-193 initial_timeout "10001ms": "... must be <= [10s]" (with max_timeout 300 s, so that only this bound fails)
example : (!valid ⟨10001, 100, 300000, 500⟩ && valid ⟨10000, 100, 300000, 500⟩) = true := by decide
-- E197-199 back_off_time "0s": "... must be >= [1ms]"
example : (!valid ⟨100, 0, 10000, 500⟩ && valid ⟨100, 1, 10000, 500⟩) = true := by decide
-- E203-208 back_off_time "60001ms": "... must be <= [60s]"
example : (!valid ⟨100, 60001, 10000, 500⟩ && valid ⟨100, 60000, 10000, 500⟩) = true := by decide
-- E212-214 max_timeout "199ms": "... must be >= [200ms]"
example : (!valid ⟨100, 100, 199, 500⟩ && valid ⟨100, 100, 200, 500⟩) = true := by decide
-- E218-220 max_timeout "301s": "... must be <= [300s]"
example : (!valid ⟨100, 100, 301000, 500⟩ && valid ⟨100, 100, 300000, 500⟩) = true := by decide

/-- E224-226: `initial_timeout` from 1 to 10000, `back_off_time` from 1 to 60000, `max_timeout` from
`max(200, initial_timeout)` to 180000 (`duration` is the default). -/
def validDraws : List (Nat × Nat × Nat) :=
  [(1, 1, 200), (10000, 60000, 180000), (10000, 1, 10000), (200, 60000, 200), (5000, 30000, 5000), (150, 7, 179999),
   (100, 100, 10000)]

-- E234-236 the three settings read back as the values put (`TimeValue` parsing, not modelled);
-- E238 assertThat(new ElectionSchedulerFactory(settings, random(), null), not(nullValue())) // doesn't throw an IAE
example : validDraws.all (fun (i, b, m) => valid ⟨i, b, m, 500⟩) = true := by decide

/-- E242-243: `initial_timeout` from 201 to 10000, `max_timeout` from 200 to `initial_timeout - 1`. -/
def invalidDraws : List (Nat × Nat) := [(201, 200), (10000, 9999), (10000, 200), (5000, 4999), (777, 500)]

-- E250-253 expectThrows(IllegalArgumentException.class, () -> new ElectionSchedulerFactory(settings, random(), null));
-- E254-263 message "[cluster.election.max_timeout] is [...], but must be at least [cluster.election.initial_timeout]
--          which is [...]" (not modelled). Each value is within its own bounds (valid when the two timeouts are equal),
--          so the constructor's check (ESF:133) is what fails.
example : invalidDraws.all (fun (i, m) =>
    !valid ⟨i, 100, m, 500⟩ && valid ⟨i, 100, i, 500⟩ && valid ⟨m, 100, m, 500⟩) = true := by decide

/-! ## testRandomPositiveLongLessThan (ElectionSchedulerFactoryTests.java:267) -/

/-- E268: `0, 1, -1, Long.MIN_VALUE, Long.MAX_VALUE, randomLong()`, with three draws of `randomLong()`. -/
def inputs : List Int := [0, 1, -1, MINL, MAXL, 6148914691236517205, -6148914691236517206, -123456789012345678]
/-- E269 -/
def upperBounds : List Nat := [1, 2, 3, 100, MAXN]

-- E270 long l = toPositiveLongAtMost(input, upperBound); E271 assertThat(l, greaterThan(0L))
example : inputs.all (fun i => upperBounds.all (fun u => decide (0 < toPositiveLongAtMost i u))) = true := by decide
-- E272 assertThat(l, lessThanOrEqualTo(upperBound))
example : inputs.all (fun i => upperBounds.all (fun u => decide (toPositiveLongAtMost i u ≤ u))) = true := by decide

-- Supplementary, not a Java assertion: the values equal those Java computes (ESF:158-172 run verbatim under OpenJDK 21,
-- rows = inputs, columns = upper bounds). `Math.abs(Long.MIN_VALUE)` is `Long.MIN_VALUE` in Java; `nonNegative` maps it
-- to 0, so its row is all 1 (with `Int.natAbs` alone, `2^63 % 3 + 1` would be 3).
example : (inputs.map (fun i => upperBounds.map (toPositiveLongAtMost i)) ==
    [[1, 1, 1, 1, 1], [1, 2, 2, 2, 2], [1, 2, 2, 2, 2], [1, 1, 1, 1, 1], [1, 2, 2, 8, 1],
     [1, 2, 3, 6, 6148914691236517206], [1, 1, 1, 7, 6148914691236517207], [1, 1, 1, 79, 123456789012345679]]) =
    true := by decide
-- Supplementary: `nonNegative` at the edges of the `long` range.
example : (nonNegative MINL == 0 && nonNegative (MINL + 1) == MAXN && nonNegative MAXL == MAXN &&
    nonNegative (-1) == 1 && nonNegative 0 == 0) = true := by decide

/-! ## Java `assert`s executed by the passing tests

OpenSearch runs its tests with assertions enabled, so every `assert` a passing test reaches held. Besides P147
(checked with each round above) and ESF:170 (checked at `testRetriesOnCorrectSchedule`):
* `handleJoin`'s `assert !prevElectionWon || electionWon` (CoordinationState.java:323) at each join of
  `testPrevotingIndicatesElectionSuccess`, checked below. Its `assert join.targetMatches(localNode)` (CS:265) holds by
  construction (P318), and `handleStartJoin`'s `assert getCurrentTerm() == startJoinRequest.getTerm()` (CS:240) by the
  transcription's definition.
* Not modelled: `PreVoteCollector`'s `assert state != null` (PVC:137; the fixture calls `update` first, P150, and the
  transcription's handler always has a state), `assert noneMatch(Coordinator::isZen1Node)` (PVC:188; there are no Zen1
  nodes here), `assert isNotAlreadyClosed` (PVC:298) and the scheduler's `assert wasNotPreviouslyClosed` (ESF:251): each
  test closes each round and scheduler once. -/

/-- The joins handled one by one, rejections ignored: `electionWon` never goes from true to false (CS:323). -/
def wonNeverLost (cs : CoordinationState Nat) (js : List Join) : Bool :=
  (js.foldl (fun (acc : CoordinationState Nat × Bool) j =>
    match acc.1.handleJoin ES j with
    | .ok (cs', _) => (cs', acc.2 && (!acc.1.electionWon || cs'.electionWon))
    | .error _ => acc) (cs, true)).2

-- CoordinationState.java:323 assert !prevElectionWon || electionWon, at P315-323
example : prevotingCases.all (fun c => okAnd c.startJoin (fun (cs, _) =>
    wonNeverLost cs c.joins && wonNeverLost cs c.joins.reverse)) = true := by decide

end OpenSearchPreVoteVectors
