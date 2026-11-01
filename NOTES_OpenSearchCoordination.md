# OpenSearch cluster coordination: `CoordinationState` and pre-voting

Two missions over OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19`,
`server/src/main/java/org/opensearch/cluster/coordination/`:

- `OpenSearchCoordination` (18 theorems): `Definitions/Def_OpenSearchCoordination.lean`,
  `Solutions/Sol_OpenSearchCoordination_all.lean`, `tests/OpenSearchCoordinationVectors.lean`.
- `OpenSearchPreVote` (10 theorems): `Definitions/Def_OpenSearchPreVote.lean` (imports the first),
  `Solutions/Sol_OpenSearchPreVote_all.lean`, `tests/OpenSearchPreVoteVectors.lean`.

Prose: `missions/items/oscoord_items.py`, `missions/items/osprevote_items.py`,
`missions/descriptions/oscoord_description.md`, `missions/descriptions/osprevote_description.md`,
`missions/explanations/expl_OpenSearch{Coordination,PreVote}_*.md`. The items leave no milestone on
`OpenSearchCoordination.javaInvariant_preserved` and `OpenSearchPreVote.preVote_then_election`, the
intended goal theorems.

Citations in the Lean files: `CS` CoordinationState.java, `CM` CoordinationMetadata.java, `ES`
ElectionStrategy.java, `CLS` ClusterState.java, `PVC` PreVoteCollector.java, `ESF`
ElectionSchedulerFactory.java, `CO` Coordinator.java, followed by line numbers at the pinned revision.

## The model

**One node (`OpenSearchCoordination`).** `CoordinationState V` has the fields of the Java class
(CS:64-106): the local node; the persisted `currentTerm` and `lastAcceptedState`; the transient
`joinVotes`, `startedJoinSinceLastReboot`, `electionWon`, `lastPublishedVersion`,
`lastPublishedConfiguration`, `publishVotes`. `CoordinationState.init` is the constructor, which a
restart runs over the persisted state. The seven handlers (`setInitialState`, `handleStartJoin`,
`handleJoin`, `handleClientValue`, `handlePublishRequest`, `handlePublishResponse`, `handleCommit`)
make the Java checks in the Java order and return `Except String`: a rejection message, or the new
state, paired with the handler's output for the five that have one. `javaInvariant`
is the conjunction of the five assertions of `invariant()` (CS:601-611); `initialStateContract` and
`clientValueContract` are the asserted preconditions of `setInitialState` (CS:190-201) and
`handleClientValue` (CS:397-398).

**Pre-voting (`OpenSearchPreVote`).** `CollectorState` (known leader, own response) and
`handlePreVoteRequest` (PVC:133-163); `PreVotingRound` with `start`, `handlePreVoteResponse`
(PVC:225-279, returning the new round, whether `startElection` is called, and the argument of
`updateMaxTermSeen`) and `close`; `NoFresher`, the condition on the responses a round records;
`RoundReachable es Delivered`, the rounds reachable when the network delivers, in any order and any
number of times, the responses that `Delivered` allows; `handleJoins`, a list of joins handled in
order with rejections ignored; `startElectionTerm` (CO:593); `nodeMayWinElection` (CO:628-633, not
used by the theorems); the scheduler settings, `Valid`, `maxDelay`, `nonNegative`,
`toPositiveLongAtMost`, `attemptDelay` (ESF:85-204).

## Abstractions, and why each is sound or what it loses

1. **Node ids are naturals; a `DiscoveryNode` is an id and the cluster-manager role.** Java ids are
   strings, and the transcribed code only tests them for equality (map keys, set membership), so any
   injective encoding behaves the same. The role is part of the node value; the cluster model assumes
   it never changes.

2. **Terms are `Nat`, versions are `Int`.** Both are Java `long`s. `CoordinationState` does no
   arithmetic on them, only comparisons and copies. A term is written only by `handleStartJoin`, with
   a strictly larger value, and starts at 0, so it is never negative (this is Java: the transcription's
   `init` takes the persisted term as a parameter, and the cluster model of `OpenSearchSafety` starts
   every node in term 0). `Int` contains every `long`
   version, including `ClusterState.UNKNOWN_VERSION = -1`. What is lost is overflow: `Coordinator`
   builds election terms as `max(currentTerm, maxTermSeen) + 1` (CO:593), which wraps at `2^63 - 1` in
   Java and not here; `startElectionTerm` is computed in `Nat`.

3. **A cluster state keeps nine fields.** Term, version, metadata version, the last committed and last
   accepted configurations, the cluster-manager node (as an ephemeral id), the cluster-UUID known and
   committed flags, and a payload `value : V` for everything else. These are all the fields
   `CoordinationState` reads or writes, apart from those it reads only to decide whether to write the
   REMOTE state (item 7); the payload is carried unchanged. `markCommitted` transcribes
   `markLastAcceptedStateAsCommitted` with `commitVotingConfiguration` (CS:703-740). Nothing about the
   payload (indices, routing, nodes) can be stated.

4. **`VotingConfiguration` is a strictly increasing list of ids.** Java stores a `Set<String>` and
   `equals` compares the sets. A strictly increasing list is a canonical form of a finite set: two
   configurations are `=` exactly when they have the same members, which is what
   `handleClientValue`'s reconfiguration test and `markCommitted` need, and `DecidableEq` compares the
   lists. `hasQuorum` counts the members occurring in the votes, the size of Java's intersection
   (CM:405-409), because a configuration has no repeated member; the vote list may repeat ids
   harmlessly. Nothing is lost.

5. **A `VoteCollection` keeps the voters' ids only.** Java keeps a `Map<String, DiscoveryNode>` keyed
   by id and a `Set<Join>` (CS:750-814). The handlers use a collection only through `addVote`,
   `isQuorum`, `containsVoteFor` and `isEmpty`, which read the keys. The joins are read only by
   `containsJoin` (test-only, CS:164-167) and by `equals`/`hashCode`. Java's `put` replaces the stored
   node of an id that is already present; the transcription leaves the list unchanged, the same set of
   ids. Lost: Java's `equals` compares the maps and the joins, while `=` here is list equality and
   depends on the order of the votes (the discrepancy in the vectors below) and, for lists not built by
   `addVote`, on repeated ids; and the strategy cannot
   read the voters' `DiscoveryNode`s or joins (item 10).

6. **Java `assert`s are caller contracts.** Assertions are off unless the JVM runs with `-ea`, as
   OpenSearch's tests do, so production behaviour is the code without them, and that is what the
   handlers transcribe. Asserted preconditions are kept as separate predicates for the cluster model to
   impose at the steps that call the methods (`initialStateContract`, `clientValueContract`). Asserted
   postconditions are theorems (CS:572 in `handleCommit_spec`; CS:323-324 as `handleJoin_stays_won`,
   for a monotone strategy at a node whose `electionWon` agrees with its votes; CS:240 in
   `handleStartJoin_spec`; CS:457 in `handlePublishRequest_spec`, at a node whose accepted term is at
   most its current term), and the assertions of `invariant()` are the predicate `javaInvariant`,
   proved to hold after the constructor (when the persisted accepted term is at most the persisted
   current term) and after `handleStartJoin` (when the accepted term is at most the current term), to
   be preserved by `handleJoin`, `handleClientValue` and `handlePublishResponse` (for a monotone
   strategy), and shown not to be preserved by `handlePublishRequest` (for the default strategy). Not
   represented: `join.targetMatches(localNode)` (CS:265; the cluster model delivers a join only to its
   target), the assertion in `markLastAcceptedStateAsCommitted` that a state with an unknown cluster
   UUID is committed only in term 0 (CS:708-710), and the assertions of the `Join` and
   `PublishResponse` constructors that their versions are non-negative (Join.java:62,
   PublishResponse.java:53; versions are unbounded integers here, while the assertions on their terms,
   Join.java:60-61 and PublishResponse.java:52, hold because terms are naturals). In the pre-vote file,
   Java's `assert state != null` (PVC:137, a node answers only after the first `update`) holds by
   construction, and `toPositiveLongAtMost`'s `assert 0 < upperBound` (ESF:170) is proved
   (`attemptDelay_bounds`).

7. **The REMOTE persisted state is omitted.** With a remote cluster-state store configured,
   `handlePublishRequest` on a non-leader also writes the accepted state and manifest to the REMOTE
   persisted state (CS:454-456, 617-632), `handleCommit` marks it committed (CS:569-571, 634-642), and
   `handlePublishResponse` marks it committed on the leader before returning a commit
   (`handlePreCommit`, CS:510, 593-599). The handlers read the REMOTE state only in the tests deciding
   whether to write it (CS:616-642); no returned value and no LOCAL write depends on it. The only
   behavioural effect is a failed remote write: the Java method then throws after its local effects
   (after `setLastAcceptedState` at CS:453, after `publishVotes.addVote` at CS:503), so the node's
   state changes and no response or commit is sent. The transcription returns the output instead;
   Java's run is the transcription's run with that output lost, which a cluster model with lossy
   messages includes. Lost: anything about the remote store itself, and the remote publication path,
   which the cluster model assumes reconstructs the published state exactly.

8. **The Zen1 compatibility branch is kept.** `handlePublishRequest` accepts a term-0 state that is not
   newer when it names a cluster-manager and the last accepted state names none or a different one
   (CS:428-446), because a Zen1 cluster-manager does not guarantee increasing versions; `getVersionOrMetadataVersion` uses the
   metadata version for term-0 states (CLS:239-244), and joins and pre-vote responses carry it. Java's
   `NullPointerException` when the incoming term-0 state names no cluster-manager is a rejection. The
   cost is visible in the theorems: `handlePublishRequest_spec` has the disjunct
   `req.acceptedState.term = ZEN1_BWC_TERM`, and a term-0 accepted state can be replaced by an older
   one.

9. **Nodes are compared by id and role; Java compares ephemeral ids.** `DiscoveryNode.equals` compares
   ephemeral ids (DiscoveryNode.java:606-617), regenerated each time a node starts. The comparisons that
   matter here: `leader.equals(request.getSourceNode())` in `handlePreVoteRequest` (PVC:153) and the
   keys of a round's `preVotesReceived` map (PVC:176, 240); `CoordinationState` compares nodes only in
   a log message (CS:231) and compares cluster-managers by ephemeral id, kept as such (CS:430). The two
   equalities differ only between two incarnations of one node with the same role. A follower of `c`'s
   previous incarnation with the same role refuses `c`'s pre-vote request in Java and answers it here,
   so Java's answers are a subset of the transcription's. In a round, two incarnations of one sender
   with the same role are two entries in Java and one here (with different roles, two in both), but
   both count one vote per id, so a Java round and the model's round fed with the same answers have
   the same votes and make the same decisions. As far as node equality is concerned, `no_disruption`
   therefore carries over to Java's rounds whenever its hypothesis holds (its other abstractions, such
   as states fixed during the round, remain); that hypothesis does not count a node following `c`'s
   previous incarnation with the same role as following another leader.

10. **An `ElectionStrategy` sees voter ids only.** Java passes the `VoteCollection` to
    `satisfiesAdditionalQuorumConstraints`, so a plugin strategy could read the voters' `DiscoveryNode`s
    (roles, attributes) or the recorded joins; in a pre-voting round those joins are synthesized from
    the responses (PVC:247-257). Here the strategy is any function of the local node, the terms and
    version, the two configurations and the voter ids. `DEFAULT_INSTANCE`, the only strategy in
    OpenSearch itself, is constant `true` and transcribed exactly. The per-node theorems are stated for
    every strategy, with `Monotone` where a won election must stay won (`handleJoin_stays_won`, and all
    three clauses of `javaInvariant_preserved`), except `default_monotone` and the counterexample
    `javaInvariant_not_local`, which concern the default one; the strategy is passed to
    `isElectionQuorum`, `handleJoin` and `javaInvariant` rather than stored in the state as in Java,
    and each theorem uses a single strategy (the cluster model of `OpenSearchSafety` gives every node
    the same one); `no_disruption` holds for every strategy, `preVote_then_election` for the default
    one.

11. **The pre-vote `updateMaxTermSeen` side effect is not modelled.** `handlePreVoteRequest` first calls
    `updateMaxTermSeen(request.getCurrentTerm())` (PVC:134), and `handlePreVoteResponse` calls it with
    the response's current term for every response handled while the round is open, before the
    freshness test (PVC:231). `handlePreVoteResponse` returns that argument (`none` when the round is
    closed); `handlePreVoteRequest` returns nothing, its argument being always the request's term. The
    effect on the `Coordinator` — raising `maxTermSeen`, and making a leader whose current term is below
    it move to that term and start an election, at once or when its publication in progress ends
    (CO:560-581, CO:1784) — is outside the functions. `no_disruption` therefore says that the requester's
    pre-voting round never calls `startElection`, not that the leader keeps its term; `preVote_then_election` takes `maxTermSeen`
    as a parameter bounded below by the recorded responses' terms (`hseen`).

12. **`Coordinator.handleJoin`'s term bump is excluded by hypothesis.** `Coordinator.handleJoin`
    (CO:1267-1299) first calls `ensureTermAtLeast(getLocalNode(), join.getTerm())` (CO:1269): a join of
    a term above the current one makes the node handle a start-join for that term from itself, which
    moves it to that term and discards its votes, and handle its own join; only then is the incoming
    join passed to `CoordinationState.handleJoin`, whose rejection the `Coordinator` swallows (election
    won) or propagates to the joining node. `handleJoins` transcribes the second part only: each join
    goes to `handleJoin`, and a rejection leaves the state unchanged, as in Java, where every check
    precedes every write. `preVote_then_election` assumes `hjs`, every join `c` handles has a term at
    most `T`; joins of a lower term are rejected the same way in both. Lost: an election interrupted by
    a join of a higher term, about which the theorem says nothing.

13. **Rejections are values.** Java throws `CoordinationStateRejectedException` (and
    `NullPointerException` in the Zen1 branch); the transcription returns `.error` with a message
    containing the substring OpenSearch's tests match. Every handler makes all its checks before its
    first write, so a rejected call leaves the state unchanged in both.

14. **Scheduler: milliseconds as `Nat`, the random long as any integer.** The settings' ranges and the
    constructor check (ESF:85-143) are `SchedulerSettings.Valid`; the scheduler reads the settings only
    through `millis()` (ESF:133, 203-204), and a value Java accepts in a setting's range has its
    `millis()` within `Valid`'s bounds, because those bounds are whole milliseconds. `maxDelay` computes
    `initialTimeout + k · backoffTime` in `Nat`; Java's `long` product could overflow after about
    `2^63 / 60000` attempts, which the Java comment at ESF:202 dismisses. `nonNegative` is exact on the
    `long` range, including `Long.MIN_VALUE`, for which `Math.abs` is negative in Java. The theorems
    hold for every drawn number; the distribution of `Random.nextLong()` is not modelled. Only the
    delay of attempt `k` is transcribed, not the scheduling (thread pool, `isClosed`, the rescheduling
    of attempt `k + 1` when attempt `k` fires, ESF:195-241).

15. **Health is a Boolean; the requester's own response is free at each step.** `getHealth()` becomes
    `healthy : Bool`, true when the status is not `UNHEALTHY`, the only status `handlePreVoteRequest`
    tests (PVC:143). Java reads the requester's current response when each answer arrives (PVC:245);
    the model takes an arbitrary `lr` at each step of `RoundReachable`, which includes every value Java
    can read. `preVote_then_election` also assumes `r.localNode = csc.localNode`, which its proof does
    not use.

## Public theorems

`OpenSearchCoordination` (every one in `Sol_OpenSearchCoordination_all.lean`):

- `quorum_intersect`: `c.hasQuorum a → c.hasQuorum b → ∃ x ∈ c.nodeIds, x ∈ a ∧ x ∈ b`.
- `quorum_mono`: a superset of a quorum is a quorum. `empty_no_quorum`: `EMPTY_CONFIG.hasQuorum a = false`.
  `no_votes_no_quorum`: `VoteCollection.empty.isQuorum c = false`.
- `addVote_eligible`: `x ∈ (v.addVote n).1.nodes ↔ x ∈ v.nodes ∨ (x = n.id ∧ n.isClusterManagerNode)`.
- `handleStartJoin_spec`: `handleStartJoin` succeeds iff `currentTerm < req.term`, with the result fixed
  field by field and the join `⟨localNode, req.sourceNode, req.term, lastAcceptedTerm,
  lastAcceptedVersionOrMetadataVersion⟩`.
- `handlePublishRequest_spec` (needs `lastAcceptedTerm ≤ currentTerm`): the accepted state is the
  incoming one, of the current term, strictly newer in (term, version) or of term 0; transient fields
  unchanged; the response is (term, version).
- `handleCommit_spec`: the commit matches the current term and the accepted term and version; only
  `markCommitted` is applied; committed = accepted configuration afterwards.
- `lastAcceptedTerm_le_currentTerm`: from `lastAcceptedTerm ≤ currentTerm`, every successful handler
  call (of `setInitialState`, with a term-0 state) preserves the inequality; `handleStartJoin` raises
  the current term, and the other handlers leave it unchanged.
- `handleJoin_spec`: the five checks passed, the vote added, `electionWon` recomputed with `cs`'s
  configurations, `lastPublishedVersion` set to the accepted version exactly when the election is
  just won, all else unchanged.
- `default_monotone`; `handleJoin_stays_won` (monotone strategy, `electionWon` agreeing with the votes
  before).
- `handleClientValue_spec`, `handlePublishResponse_spec`: what a successful call implies — the
  conditions for publishing a value, respectively for emitting a commit — and the resulting state.
- `init_javaInvariant` (`s.term ≤ t`), `handleStartJoin_javaInvariant` (`lastAcceptedTerm ≤
  currentTerm`), `javaInvariant_preserved` (monotone strategy; `handleJoin`, `handleClientValue`,
  `handlePublishResponse`), `javaInvariant_not_local` (for the default strategy, an explicit node
  violating `invariant()` after `handlePublishRequest`).

`OpenSearchPreVote` (every one in `Sol_OpenSearchPreVote_all.lean`):

- `handlePreVoteRequest_spec`: answers iff healthy and (no leader or the requester is the leader),
  with the node's own response.
- `votes_mem`: the round's votes are its eligible recorded senders.
- `round_entries` (any reachable round): entries no fresher than the round's state, delivered, one per
  sender.
- `round_start_quorum`, `round_starts_once`: `startElection` is called only from an open, not yet
  started round whose votes, once the new response is recorded, are an election quorum; once a round
  has started an election or been closed, handling a response never calls it again.
- `no_disruption` (any strategy; every node's health and collector state fixed while the round runs):
  if every node of a quorum `L` of one of the configurations of `s` is unhealthy or follows a leader
  other than `c`, no round of `c` over `s`, fed with the nodes' answers to `c`'s request, has started
  an election, and handling one more such answer does not start one.
- `preVote_then_election`: default strategy; a round over `c`'s last accepted state, with `c` as local
  node, that has started an election; senders unchanged since answering (a response from `n` is
  `preVoteResponseOf (node n)`, where `node n` has local node `n`); `maxTermSeen` at least the current
  term of every recorded response and `T = max(currentTerm, maxTermSeen) + 1`; after its own
  start-join for `T`, `c` handles only joins, all of term at most `T`: every recorded sender accepts
  `c`'s start-join for `T`, and if their joins are among the joins `c` handles, `c` wins
  (`electionWon = true`).
- `attemptDelay_bounds`, `maxDelay_schedule` (valid settings), `nonNegative_two_to_one` (Java `long`
  range).

## Proof structure

- Quorums: two private counting lemmas on `List.filter` (`filter_length_add_le`,
  `filter_length_mono`), then `omega`.
- Handler specifications: unfold, walk the guard chain with `split at h`, close each rejection by
  `cases h`, identify the successful result by injectivity, and read each conjunct off a negated guard
  (`Classical.not_not`, `simpa`, `omega`). The invariant theorems combine the specifications.
- `javaInvariant_not_local`: an explicit witness checked by `decide` and `rfl`.
- Pre-voting: the mission imports the per-node definitions but none of its theorems; the per-node
  lemmas the proofs need are proved again privately with a `pv_` prefix (`pv_quorum_intersect`,
  `pv_quorum_mono`, `pv_addVote_eligible`, `pv_handleStartJoin_spec`, ...). New private lemmas: `pv_handle_shape` (the
  effect of one response on a round), `pv_handleJoins_spec` (induction over a join list),
  `pv_handleJoin_succeeds`, `pv_started_quorum`, `pv_not_election_quorum`, `pv_votes_grow`.
  `no_disruption` and `round_entries` are inductions over `RoundReachable`.
- Scheduler: `omega` with one multiplication fact each (`Nat.mul_le_mul_right`, `Nat.succ_mul`,
  `Nat.le_mul_of_pos_right`, `Nat.mod_lt`).

## Test vectors (`tests/OpenSearchCoordinationVectors.lean`)

- **41 Java tests**: 40 of the 47 tests of `CoordinationStateTests.java` and `testVotingConfiguration`
  of `CoordinationMetadataTests.java`. **179 checks**, each an `example` proved by `decide` under a
  comment quoting the Java line it replays. `lake env lean tests/OpenSearchCoordinationVectors.lean`
  succeeds in about 6 seconds with no message.
- Not replayed: `testSafety` (a randomized cluster run; its properties are proved for the cluster model
  of `OpenSearchSafety`: `one_master_per_term`, `one_state_per_version`, and `javaInvariant_reachable`,
  every node being cluster-manager-eligible in the test) and the
  six tests of the REMOTE state and remote publication
  (`testHandlePrePublishAndCommitWhenRemoteState{Disabled,Enabled}`,
  `testHandlePublishRequestOnFollowerWhenRemotePublicationEnabled`,
  `testHandleCommitOnFollowerNodeWhenRemotePublicationEnabled{,WithNullRemotePersistedState}`,
  `testRemotePersistedStateResetsForPublicationEnabledAfterLocalPublication`).
- Fixture: `createNode("nodeK")` is `⟨K, true⟩`; the tests' `clusterState(...)` helper gives metadata
  version 0, a known uncommitted cluster UUID and no elected cluster-manager; Java's identity equality
  on cluster states becomes structural equality of the reduced states; each random draw becomes 2 to 5
  concrete instances including the bounds of its range; a call outside `expectThrows` must succeed
  (`okAnd`); `expectThrows(..., containsString(m))` is "rejected with a message containing `m`".
  `containsJoin(j)` is replayed as "`handleJoin(j)` returned true and the vote of `j`'s source is
  present", which is when Java records the join.
- The two tests that expect an `AssertionError` (`testJoinWithWrongTarget`,
  `testHandleClientValueWithIllegalCommittedConfigurationChange`) rely on `assert`s the transcription
  does not check; they are recorded as comments, with a supplementary check of the production
  behaviour (the join is rejected because the node is not bootstrapped; the value is accepted while
  `clientValueContract` fails).
- **The `VoteCollection.equals` discrepancy.** `testVoteCollection` ends with
  `checkEqualsAndHashCode(voteCollection, copy, mutate)`. Its copy re-adds the votes in iteration
  order; `addVote` prepends, so the copy of `⟨[2, 1]⟩` is `⟨[1, 2]⟩`. Four copy-equality assertions —
  `original.equals(copy)`, `copy.equals(original)`, `copy.equals(secondCopy)`,
  `secondCopy.equals(copy)` — hold for Java's map equality and fail for the transcription's `=`. They
  are commented out; the file checks them with set equality of the voters (`sameVoters`) and records
  that `=` gives `false` for all four. No handler compares vote collections.
- The Java assertions reached by the passing tests are checked separately: `initialStateContract` at
  the three bootstraps, `clientValueContract` at the calls of `handleClientValue` that pass its checks,
  and CS:572 after the commit of `testHandleCommit`.
- The pre-vote mission's vectors are in `tests/OpenSearchPreVoteVectors.lean`: the 14 tests of
  `PreVoteCollectorTests.java` and the 3 of `ElectionSchedulerFactoryTests.java`, 39 checks, each an
  `example` proved by `decide`; `lake env lean tests/OpenSearchPreVoteVectors.lean` succeeds with no
  message.

## Checks

- `lake env lean` on both `_all` files with `#print axioms` for each of the 28 public theorems: only
  `propext`, `Classical.choice` and `Quot.sound`; `empty_no_quorum`, `default_monotone` and
  `javaInvariant_not_local` use none, `handlePreVoteRequest_spec` and `round_starts_once` only
  `propext`.
- The 28 split files `Solutions/Sol_OpenSearch{Coordination,PreVote}_<name>.lean` compile without
  errors; their only `sorry`s are the imported `Theorems/` stubs. Their `import Theorems.Thm_...` lines
  fix the dependency order of `ORDER` in the items files. The three scheduler theorems import
  `votes_mem` although their proofs do not use it, because each split file carries all preceding
  private lemmas, and `pv_votes_grow` uses `votes_mem`.

## What is not proved

- **Cluster-level properties.** At most one leader per term, one published state per term and version,
  committed states never fork, the assertions of `invariant()` at every cluster-manager-eligible node
  of every execution: the `OpenSearchSafety` mission (`one_master_per_term`, `election_safety`,
  `one_state_per_version`, `committed_linear`, `javaInvariant_reachable`, all assuming compatible
  bootstrap configurations and the default election strategy), whose cluster model is in
  `Definitions/Def_OpenSearchSafety.lean` (every node runs the transcribed `CoordinationState`;
  messages may be lost, duplicated and reordered; nodes restart, and a node that is not
  cluster-manager-eligible may come back with any term and state, so `invariant()` can fail there).
  `javaInvariant_not_local` shows that the last of these cannot be proved node by node.
- **`invariant()` under `handleCommit` and `setInitialState`.** Neither is covered by any theorem;
  both change the configurations the second assertion reads. `handleCommit` does not preserve
  `javaInvariant` in isolation either (checked by evaluation, not stated as a theorem): for the default
  strategy, a node satisfying it with join votes `[4]`, `electionWon` false, committed configuration
  {1, 2, 3} and accepted configuration {4} applies a valid commit and then has an election quorum
  while `electionWon` is still false.
- **Liveness.** Nothing says an election eventually succeeds, that the random delays separate competing
  candidates, or how long anything takes. `preVote_then_election` is a one-round prediction under the
  hypothesis that nothing changes.
- **The rest of the `Coordinator`.** Mode changes (candidate, leader, follower), the publication
  pipeline and its timeouts, `LagDetector`, `FollowersChecker`, `LeaderChecker`, join validation,
  `Reconfigurator` and voting-configuration exclusions, `ClusterBootstrapService`, abdication.
- **The Java runtime.** Concurrency (the `Coordinator` mutex, the collector's volatile state), I/O
  failures of the persisted states, `long` overflow.
- **The remote cluster-state store.**
