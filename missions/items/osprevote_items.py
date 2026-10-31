SRC = ("OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: PreVoteCollector (state line 79, start 111-115, update 128-131, "
       "handlePreVoteRequest 133-163, PreVotingRound 175-300, handlePreVoteResponse 225-279, close 296-299): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PreVoteCollector.java#L66-L301; "
       "Coordinator (updateMaxTermSeen lines 560-581, startElection 583-602, nodeMayWinElection 628-633, getPreVoteResponse 873-879, "
       "handleJoin 1267-1299, startElectionScheduler 1567-1618, the preVoteCollector.update calls 516, 653, 777, 801, 839, 1157): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L560-L633; "
       "ElectionSchedulerFactory (settings lines 85-115, constructor check 133-143, nonNegative 159-161, toPositiveLongAtMost 169-172, "
       "scheduleNextElection 195-241): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; "
       "ElectionStrategy.isElectionQuorum (lines 68-88): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L68-L88; "
       "the messages PreVoteRequest.java and PreVoteResponse.java in the same directory; "
       "CoordinationState (handleStartJoin, handleJoin) as transcribed by the OpenSearchCoordination mission")
TAGS = ["opensearch", "elasticsearch", "consensus", "cluster-coordination", "zen2", "raft", "paxos", "pre-vote",
        "leader-election", "election-scheduler", "formal-verification"]

DEFINITION = {
    "definition_name": "OpenSearchPreVote",
    "definition_title": "OpenSearch pre-voting: pre-vote requests and responses, pre-voting rounds, the election they trigger, and the election scheduler's delays",
    "natural_language_statement": r"""A transcription of `PreVoteCollector`, the parts of `Coordinator` it calls, and the delay computation of `ElectionSchedulerFactory`, at OpenSearch revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, over the per-node `CoordinationState` of the `OpenSearchCoordination` mission (whose `DiscoveryNode`, `ClusterState`, `VoteCollection`, `ElectionStrategy`, `Join`, `CoordinationState`, `handleStartJoin` and `handleJoin` are used as they are).

**Messages.** **`PreVoteRequest`** — the requesting node and its current term. **`PreVoteResponse`** — the responder's current term, and the term and the version (the metadata version, for a term-0 state) of its last accepted state. **`preVoteResponseOf cs`** — the response a node with coordination state `cs` gives: `cs.currentTerm`, `cs.lastAcceptedTerm`, `cs.lastAcceptedVersionOrMetadataVersion` (`Coordinator.getPreVoteResponse`).

**Answering.** **`CollectorState`** — the known leader (`none` when no leader is known) and the node's own response, as last set by the `Coordinator` (itself when it becomes leader, the leader it follows, `none` when it becomes a candidate). **`handlePreVoteRequest healthy st req`** — rejects if the node is not healthy; otherwise answers with `st.response` if the node knows no leader or knows `req.sourceNode` as its leader, and rejects if it knows another leader.

**Rounds.** **`PreVotingRound V`** — the requester's last accepted cluster state when the round started, the requester (`localNode`), the recorded pre-votes as a list of (sender, response) pairs, most recent first, and the flags `electionStarted` and `isClosed`. **`PreVotingRound.start s n`** — an open round over `s` for requester `n`, with no pre-votes and no election started. **`votes r`** — the vote collection built by adding the vote of each recorded sender to the empty collection (only cluster-manager-eligible senders count). **`isElectionQuorumFor es n t at av committed accepted votes`** — `ElectionStrategy.isElectionQuorum` with explicit arguments: `votes` is a quorum of `committed` and of `accepted`, and the strategy's additional constraint holds for the local node `n`, current term `t`, accepted term `at` and version `av`, the two configurations and `votes`.

**`r.handlePreVoteResponse es lr resp sender`** (PVC:225-279) returns the new round, whether `startElection` is called, and the term passed to `updateMaxTermSeen` (`none` if none is passed); `lr` is the requester's own current response, read when the response arrives. If the round is closed: unchanged, `false`, `none`. Otherwise, if `resp` is fresher than the round's accepted state `s` — `resp.lastAcceptedTerm > s.term`, or equal terms and `resp.lastAcceptedVersion > s.versionOrMetadataVersion` — the round is unchanged, with `false` and `some resp.currentTerm`. Otherwise the pair `(sender, resp)` replaces any earlier entry of `sender`; if the new votes are not an election quorum (`isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion` over the last committed and last accepted configurations of `s`), or the round has already started an election, the result is that round with `false`; otherwise the round with `electionStarted` set, and `true`. In every case but the closed one, the term passed is `some resp.currentTerm`. **`close r`** — the round with `isClosed` set.

**`NoFresher resp s`** — `resp.lastAcceptedTerm < s.term`, or `resp.lastAcceptedTerm = s.term` and `resp.lastAcceptedVersion ≤ s.versionOrMetadataVersion`: the responses a round records. **`RoundReachable es Delivered`** — the rounds obtained from `start s n` (any `s`, `n`) by handling, any number of times and in any order, responses `resp` from senders `n` with `Delivered n resp` (each step with an arbitrary requester response `lr`), and by `close`.

**The election.** **`handleJoins es cs js`** — the joins of `js` handled in order by `CoordinationState.handleJoin`; a rejected join leaves the state unchanged (as `Coordinator.handleJoin`, CO:1267-1299, for joins whose term is not above the node's current term; for a higher term the `Coordinator` first moves the node to that term). **`startElectionTerm currentTerm maxTermSeen`** — `max currentTerm maxTermSeen + 1`, the term of the `StartJoinRequest` that `startElection` sends (CO:593). **`nodeMayWinElection s excluded n`** — `n` is in the last committed or the last accepted configuration of `s`, or is not among the excluded ids (CO:628-633); it is not used by the theorems.

**The scheduler** (times in milliseconds). **`SchedulerSettings`** — `initialTimeout`, `backoffTime`, `maxTimeout`, `duration`. **`Valid`** — the setting ranges (`1 ≤ initialTimeout ≤ 10000`, `1 ≤ backoffTime ≤ 60000`, `200 ≤ maxTimeout ≤ 300000`, `1 ≤ duration ≤ 300000`) and the constructor's check `initialTimeout ≤ maxTimeout`. **`default`** — 100, 100, 10000, 500 (not used by the theorems). **`maxDelay s k`** — `min(maxTimeout, initialTimeout + k · backoffTime)`, the bound for attempt `k` (counted from 0). **`nonNegative n`** — 0 for `n = -2^63` (`Long.MIN_VALUE`), `|n|` otherwise. **`toPositiveLongAtMost r b`** — `nonNegative r mod b + 1`. **`attemptDelay s k r g`** — `toPositiveLongAtMost r (maxDelay s k) + g`, the delay of attempt `k` for the drawn random long `r` and grace period `g` (0 for the first attempt, `duration` for the later ones).

**Formalization Note.** The `Coordinator`'s side effects are not modelled. The argument of `updateMaxTermSeen` is returned by `handlePreVoteResponse`, and not at all by `handlePreVoteRequest` (where it is always the request's term); the call's effect is outside these functions: in particular a leader whose current term is below the largest term it has seen moves to that term and starts an election (CO:560-581). Nodes are compared by id and role, while Java's `DiscoveryNode.equals` compares ephemeral ids, which change at each restart: the two agree except between two incarnations of one node. The election strategy sees voter ids only (the per-node mission's abstraction). Health is a Boolean parameter, the network is the delivery predicate of `RoundReachable`, and the random long is any integer: the theorems hold for every value. Only the per-node mission's definitions are imported.""",
}

THEOREMS = {
"OpenSearchPreVote.handlePreVoteRequest_spec": dict(
    title="A node answers a pre-vote request exactly when it is healthy and follows no other leader",
    nl=r"""For every health status `healthy`, collector state `st`, request `req` and response `resp`: `handlePreVoteRequest healthy st req = .ok resp` iff `healthy = true`, the node knows no leader or knows the requester as its leader (`st.leader = none ∨ st.leader = some req.sourceNode`), and `resp = st.response`, the node's own current response. Unhealthy nodes and nodes that follow a leader other than the requester refuse.""",
    ms=None),
"OpenSearchPreVote.votes_mem": dict(
    title="A round counts exactly its cluster-manager-eligible senders",
    nl=r"""For every pre-voting round `r` and node id `x`: `x` is among the ids of `r.votes` iff some recorded entry `p ∈ r.preVotesReceived` has `p.1.id = x` and `p.1.isClusterManagerNode = true`. The votes of a round are the ids of its recorded senders that have the cluster-manager role.""",
    ms=None),
"OpenSearchPreVote.round_entries": dict(
    title="A round records only no-fresher, delivered responses, one per sender",
    nl=r"""For every election strategy `es`, delivery predicate `Delivered` and round `r` with `RoundReachable es Delivered r` (started, then any responses allowed by `Delivered` handled in any order and any number of times, and possibly closed):

- every recorded entry `p ∈ r.preVotesReceived` satisfies `NoFresher p.2 r.clusterState` — the response's accepted (term, version) is lexicographically at most the round's accepted (term, version-or-metadata-version) — and `Delivered p.1 p.2`;
- the senders of the recorded entries are pairwise distinct: `(r.preVotesReceived.map Prod.fst).Nodup`.""",
    ms=("What a round records", "Induction over the reachable rounds: a handled response is ignored, or passes the freshness test and replaces its sender's earlier entry.")),
"OpenSearchPreVote.round_start_quorum": dict(
    title="A round starts an election only on an election quorum, while open, and not twice",
    nl=r"""For every election strategy `es`, requester response `lr`, response `resp`, sender, rounds `r` and `r'` and `m`: if `r.handlePreVoteResponse es lr resp sender = (r', true, m)` — handling the response calls `startElection` — then

- `r.isClosed = false`, `r.electionStarted = false` and `r'.electionStarted = true`;
- `NoFresher resp r.clusterState`;
- `r'` has the accepted state and the local node of `r`;
- the votes of `r'`, including the new one, form an election quorum for the round's local node and the requester's response `lr` over the last committed and last accepted configurations of the round's accepted state: `isElectionQuorumFor es r.localNode lr.currentTerm lr.lastAcceptedTerm lr.lastAcceptedVersion r.clusterState.lastCommittedConfiguration r.clusterState.lastAcceptedConfiguration r'.votes = true`.""",
    ms=None),
"OpenSearchPreVote.round_starts_once": dict(
    title="Once a round has started an election or been closed, it never starts one again",
    nl=r"""For every election strategy `es`, requester response `lr`, response `resp`, sender and round `r` with `r.electionStarted = true ∨ r.isClosed = true`: handling the response does not call `startElection` (`(r.handlePreVoteResponse es lr resp sender).2.1 = false`), and the resulting round again has `electionStarted = true` or `isClosed = true`. Hence a round calls `startElection` at most once, and never after it is closed (Java's `compareAndSet` on `electionStarted`, PVC:272).""",
    ms=None),
"OpenSearchPreVote.no_disruption": dict(
    title="Pre-voting protects a stable leader",
    nl=r"""Fix an election strategy `es`, the health `healthy n` and collector state `st n` of every node `n` (as they stand while the round runs), a requester `c` whose pre-vote requests carry the term `t`, a cluster state `s`, and a list of node ids `L` that is a quorum of the last committed or of the last accepted configuration of `s`. Suppose every node whose id is in `L` is unhealthy or knows a leader other than `c`: for every `n` with `n.id ∈ L`, `healthy n = false`, or `(st n).leader = some l` with `l ≠ c`. Let `r` be a round over `s` (`r.clusterState = s`) that is reachable when the deliverable responses are exactly the answers to `c`'s request, `handlePreVoteRequest (healthy n) (st n) ⟨c, t⟩ = .ok resp`. Then `r.electionStarted = false`, and handling any further such answer, with any requester response `lr`, does not call `startElection`.

Whatever answers arrive, in whatever order and number: only nodes outside `L` answer, and a set of voters disjoint from a quorum of a configuration is not a quorum of it, so the election-quorum test, which needs quorums of both configurations, never passes. A node cut off from a cluster whose majority follows a leader cannot depose that leader by starting elections when it reconnects. The theorem does not cover the requests' side effect: each request raises the receiver's largest seen term to at least `t`, and a leader whose current term is below `t` then moves to that larger term and starts an election itself, immediately or after its publication in progress (`Coordinator.updateMaxTermSeen`, CO:560-581, and CO:1784).""",
    ms=("No disruption by a minority node", "Answering nodes lie outside `L` (`handlePreVoteRequest_spec`) and every recorded sender answered (`round_entries`); quorum intersection then fails the election test at every step, by induction over the round.")),
"OpenSearchPreVote.preVote_then_election": dict(
    title="A successful pre-vote predicts a successful election",
    nl=r"""Let `csc` be the coordination state of a node `c`, and `node n` the coordination state in which each node `n` handles `c`'s start-join request. Let `r` be a round reachable under the default election strategy in which a response `resp` can be delivered from `n` only if `(node n).localNode = n` and `preVoteResponseOf (node n) = resp`: the senders' current term and accepted term and version have not changed since they answered. Suppose `r.clusterState = csc.lastAcceptedState`, `r.localNode = csc.localNode`, and `r.electionStarted = true`. Let `maxTermSeen` be at least the current term of every recorded response (`updateMaxTermSeen` makes it so) and `T = startElectionTerm csc.currentTerm maxTermSeen`, that is `max(csc.currentTerm, maxTermSeen) + 1`. Let `csc.handleStartJoin ⟨csc.localNode, T⟩ = .ok (csc₁, j₀)`, and let `js` be any list of joins whose terms are all at most `T`. Then:

1. every recorded sender `p.1` accepts the request: `(node p.1).handleStartJoin ⟨csc.localNode, T⟩` succeeds;
2. if every join the recorded senders produce from that request occurs in `js`, then `(handleJoins ElectionStrategy.DEFAULT_INSTANCE csc₁ js).electionWon = true`.

The senders' joins may arrive in any order, interleaved with any other joins of term at most `T`, accepted or rejected (a rejected join leaves the state unchanged), and `c` handles nothing else in between. The bound on the join terms restricts the statement to the joins `Coordinator.handleJoin` handles without first moving `c` to a higher term (CO:1269), which would discard the votes.""",
    ms=None),
"OpenSearchPreVote.attemptDelay_bounds": dict(
    title="Every election attempt waits between one millisecond and its bound, after the grace period",
    nl=r"""For valid scheduler settings `s` (`s.Valid`), every attempt number `k`, every drawn random number `r` (any integer) and every grace period `g`: `1 ≤ maxDelay s k`, and `g + 1 ≤ attemptDelay s k r g ≤ g + maxDelay s k`. With `maxDelay s k = min(maxTimeout, initialTimeout + k · backoffTime)` and `attemptDelay s k r g = (nonNegative r mod maxDelay s k) + 1 + g`, this is the range `(0, maxDelay]` of the scheduler's documentation (ESF:71-83) shifted by the grace period, and the assertion `0 < upperBound` of `toPositiveLongAtMost` (ESF:170) always holds.""",
    ms=("Election scheduling", "The bound is positive under the setting ranges; the remainder modulo the bound is below it.")),
"OpenSearchPreVote.maxDelay_schedule": dict(
    title="The delay bound backs off linearly from the initial timeout to the maximum timeout",
    nl=r"""For valid scheduler settings `s`:

- `maxDelay s 0 = s.initialTimeout`;
- `maxDelay s k ≤ maxDelay s k'` whenever `k ≤ k'`;
- for every `k` with `maxDelay s k < s.maxTimeout`, `maxDelay s (k + 1)` is `maxDelay s k + s.backoffTime` or `s.maxTimeout`;
- `maxDelay s k = s.maxTimeout` for every `k ≥ s.maxTimeout` (the number `maxTimeout` used as an attempt count: since `backoffTime ≥ 1`, the bound has reached the maximum by then).""",
    ms=None),
"OpenSearchPreVote.nonNegative_two_to_one": dict(
    title="nonNegative maps the Java longs exactly two-to-one onto [0, 2^63)",
    nl=r"""For every natural number $v < 2^{63}$ and every integer $n$ with $-2^{63} \le n < 2^{63}$ (a Java `long`): `nonNegative n = v` iff $n = v$, or $n = -v$ when $v > 0$, respectively $n = -2^{63}$ (`Long.MIN_VALUE`) when $v = 0$. Every value in $[0, 2^{63})$ has exactly two preimages among the $2^{64}$ longs, so a uniformly distributed long gives a uniformly distributed `nonNegative` value. The theorem is the counting statement; no probability is formalized.""",
    ms=None),
}
ORDER = ["OpenSearchPreVote." + k for k in ["handlePreVoteRequest_spec", "votes_mem", "round_entries", "round_start_quorum",
  "round_starts_once", "no_disruption", "preVote_then_election", "attemptDelay_bounds", "maxDelay_schedule",
  "nonNegative_two_to_one"]]
