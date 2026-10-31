# Read-back: `Def_OpenSearchPreVote.lean`

This file imports `Definitions.Def_OpenSearchCoordination`, opens that namespace (`OpenSearchCoordination`), and introduces 23 declarations in the namespace `OpenSearchPreVote`. Throughout, $V$ is an arbitrary type (the opaque payload of a cluster state); it is implicit wherever it is not written. The imported notions these declarations use are expanded first. The declarations follow in file order.

Every declaration that cites Java was compared with the OpenSearch checkout at `/home/user/opensearch-project/OpenSearch`. `git rev-parse HEAD` there gives `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, the revision the file cites. Each comparison is reported in a *Source check* line. `PVC` is `PreVoteCollector.java`, `CO` is `Coordinator.java`, `ESF` is `ElectionSchedulerFactory.java`, and all three are under `server/src/main/java/org/opensearch/cluster/coordination/`.

## Imported notions, expanded

**Node ids and discovery nodes.** A node id is a natural number. A *discovery node* $n$ is a pair: a node id $n.\mathrm{id}$ and a Boolean $n.\mathrm{cm}$ (`isClusterManagerNode`, "is cluster-manager-eligible"). Equality of discovery nodes is structural: $n = n'$ iff $n.\mathrm{id} = n'.\mathrm{id}$ and $n.\mathrm{cm} = n'.\mathrm{cm}$. So $\langle 5, \mathrm{true}\rangle \neq \langle 5, \mathrm{false}\rangle$. Two discovery nodes with the same id but different flags are different nodes.

**Voting configurations.** A voting configuration $C$ is a strictly increasing list of node ids $C.\mathrm{ids}$, so it has no duplicates, bundled with a proof of that fact. $\mathrm{isEmpty}(C)$ holds iff the list is empty. For any list $X$ of node ids,
$$\mathrm{hasQuorum}(C, X) \;=\; \Big(2\cdot\big|\{x \in C.\mathrm{ids} : x \in X\}\big| \;>\; |C.\mathrm{ids}|\Big),$$
a Boolean: strictly more than half of the configuration's ids occur in $X$. Duplicates in $X$ and elements of $X$ outside $C$ make no difference. The empty configuration never has a quorum, because $0 > 0$ is false.

**Vote collections.** A vote collection $v$ is a list $v.\mathrm{nodes}$ of node ids. $\mathrm{empty}$ is the empty list. $\mathrm{addVote}(v, n)$ returns a pair:
- $(\langle n.\mathrm{id} :: v.\mathrm{nodes}\rangle,\ \mathrm{true})$ if $n.\mathrm{cm} = \mathrm{true}$ and $n.\mathrm{id} \notin v.\mathrm{nodes}$;
- $(v, \mathrm{false})$ otherwise.

$\mathrm{isQuorum}(v, C) = \mathrm{hasQuorum}(C, v.\mathrm{nodes})$.

**Cluster states.** A cluster state $s$ has these fields:
- a term $s.\mathrm{term} \in \mathbb{N}$;
- a version $s.\mathrm{version} \in \mathbb{Z}$ and a metadata version $s.\mathrm{metadataVersion} \in \mathbb{Z}$;
- a last committed configuration $s.\mathrm{committed}$ and a last accepted configuration $s.\mathrm{accepted}$;
- an optional natural number (the cluster-manager node) and two Booleans (cluster UUID known, cluster UUID committed);
- a payload of type $V$.

Its *version-or-metadata-version* is
$$\mathrm{vomv}(s) = \begin{cases} s.\mathrm{metadataVersion} & \text{if } s.\mathrm{term} = 0 \ (\texttt{ZEN1\_BWC\_TERM}),\\ s.\mathrm{version} & \text{otherwise.}\end{cases}$$

**Election strategies.** An election strategy $es$ is just one arbitrary Boolean function $\mathrm{extra}_{es}(n, t, a, w, C_c, C_a, v)$ (`satisfiesAdditionalQuorumConstraints`). Its arguments are a discovery node, two naturals, an integer, two voting configurations and a vote collection. The default strategy `DEFAULT_INSTANCE` has $\mathrm{extra} \equiv \mathrm{true}$.

**Start-join requests and joins.** A start-join request is a pair (source node, term $\in \mathbb{N}$). A join is a 5-tuple $\langle$source node, target node, term $\in \mathbb{N}$, last accepted term $\in \mathbb{N}$, last accepted version $\in \mathbb{Z}\rangle$.

**Coordination states.** A coordination state $cs$ has these fields:
- a local node $cs.\mathrm{localNode}$ and a current term $cs.\mathrm{currentTerm} \in \mathbb{N}$;
- a last accepted state $cs.\mathrm{las}$ (a cluster state);
- a vote collection $cs.\mathrm{joinVotes}$;
- Booleans $cs.\mathrm{startedJoinSinceLastReboot}$ and $cs.\mathrm{electionWon}$;
- an integer $cs.\mathrm{lastPublishedVersion}$, a configuration $cs.\mathrm{lastPublishedConfiguration}$ and a vote collection $cs.\mathrm{publishVotes}$.

The accessors used below are:
- $\mathrm{lastAcceptedTerm}(cs) = cs.\mathrm{las}.\mathrm{term}$;
- $\mathrm{lastAcceptedVersion}(cs) = cs.\mathrm{las}.\mathrm{version}$;
- $\mathrm{lastAcceptedVersionOrMetadataVersion}(cs) = \mathrm{vomv}(cs.\mathrm{las})$;
- the two configurations $cs.\mathrm{las}.\mathrm{committed}$ and $cs.\mathrm{las}.\mathrm{accepted}$.

The three coordination-state functions used here:

- **$\mathrm{isElectionQuorum}(es, cs, v)$** is the conjunction of:
  - $\mathrm{isQuorum}(v, cs.\mathrm{las}.\mathrm{committed})$;
  - $\mathrm{isQuorum}(v, cs.\mathrm{las}.\mathrm{accepted})$;
  - $\mathrm{extra}_{es}(cs.\mathrm{localNode}, cs.\mathrm{currentTerm}, cs.\mathrm{las}.\mathrm{term}, cs.\mathrm{las}.\mathrm{version}, cs.\mathrm{las}.\mathrm{committed}, cs.\mathrm{las}.\mathrm{accepted}, v)$. The plain version is passed here, not $\mathrm{vomv}$.

  Under the default strategy it is just the two quorum tests.
- **$\mathrm{handleStartJoin}(cs, \langle src, T\rangle)$.** If $T \le cs.\mathrm{currentTerm}$ it returns an error. Otherwise it succeeds with a pair $(cs', j)$:
  - $cs'$ is $cs$ with: current term $T$, last published version $0$, last published configuration $cs.\mathrm{las}.\mathrm{accepted}$, startedJoinSinceLastReboot $=$ true, electionWon $=$ false, and both vote collections empty. The local node and the last accepted state are unchanged.
  - $j = \langle cs.\mathrm{localNode},\ src,\ T,\ cs.\mathrm{las}.\mathrm{term},\ \mathrm{vomv}(cs.\mathrm{las})\rangle$.
- **$\mathrm{handleJoin}(es, cs, j)$.** The guards are tested in this order, and the first that applies gives an error:
  1. $j.\mathrm{term} \neq cs.\mathrm{currentTerm}$;
  2. $cs.\mathrm{startedJoinSinceLastReboot} = \mathrm{false}$;
  3. $j.\mathrm{lastAcceptedTerm} > cs.\mathrm{las}.\mathrm{term}$;
  4. $j.\mathrm{lastAcceptedTerm} = cs.\mathrm{las}.\mathrm{term}$ and $j.\mathrm{lastAcceptedVersion} > \mathrm{vomv}(cs.\mathrm{las})$;
  5. $cs.\mathrm{las}.\mathrm{accepted}$ is empty.

  If none applies, let $(v', \mathit{added}) = \mathrm{addVote}(cs.\mathrm{joinVotes}, j.\mathrm{source})$ and $\mathit{won} = \mathrm{isElectionQuorum}(es, cs, v')$. Let $cs_1$ be $cs$ with joinVotes $v'$ and electionWon $\mathit{won}$. Let $cs_2$ be $cs_1$ with lastPublishedVersion set to $cs.\mathrm{las}.\mathrm{version}$ when $\mathit{won}$ is true and $cs.\mathrm{electionWon}$ was false, and $cs_2 = cs_1$ otherwise. The result is success with $(cs_2, \mathit{added})$.

  The join's target node is never examined. Neither the current term, nor the local node, nor the last accepted state changes.

---

## Declaration 1: `PreVoteRequest`

This is a structure with two fields: $\mathrm{sourceNode}$, a discovery node, and $\mathrm{currentTerm} \in \mathbb{N}$. Decidable equality and `Repr` are derived.

*Source check:* `PreVoteRequest.java` has exactly the fields `DiscoveryNode sourceNode` and `long currentTerm` (lines 50–51). The term is a natural number here instead of a Java `long`.

## Declaration 2: `PreVoteResponse`

This is a structure with three fields: $\mathrm{currentTerm} \in \mathbb{N}$, $\mathrm{lastAcceptedTerm} \in \mathbb{N}$ and $\mathrm{lastAcceptedVersion} \in \mathbb{Z}$. Decidable equality and `Repr` are derived. Nothing relates the fields to each other; for example, $\mathrm{lastAcceptedTerm} \le \mathrm{currentTerm}$ is not required.

*Source check:* `PreVoteResponse.java` has the three `long` fields `currentTerm`, `lastAcceptedTerm` and `lastAcceptedVersion` (lines 48–50).

## Declaration 3: `preVoteResponseOf`

For a coordination state $cs$:
$$\mathrm{preVoteResponseOf}(cs) = \langle cs.\mathrm{currentTerm},\ cs.\mathrm{las}.\mathrm{term},\ \mathrm{vomv}(cs.\mathrm{las})\rangle.$$
The version component is the version-or-metadata-version. It is the metadata version when the last accepted state has term $0$.

*Source check:* CO:873–879 builds `new PreVoteResponse(getCurrentTerm(), getLastAcceptedTerm(), getLastAcceptedState().getVersionOrMetadataVersion())`, and `getCurrentTerm()` (CO:882–886) reads the coordination state's current term. **Matches.**

## Declaration 4: `CollectorState`

This is a structure with two fields:
- $\mathrm{leader}$: either "none" or "some $l$" for a discovery node $l$;
- $\mathrm{response}$: a `PreVoteResponse`.

Decidable equality and `Repr` are derived. The type does not tie the response to any coordination state, or the leader to anything. Java's `null` state, before the first `update`, cannot be represented here: every value of this type is an initialized state.

*Source check:* PVC:79 declares `Tuple<DiscoveryNode, PreVoteResponse> state`, whose node is `null` when no leader is known. PVC:128–131, `update`, replaces both components. The docstring lists six `update` calls in Coordinator, and I checked each:

| Line | Leader passed to `update` |
|---|---|
| CO:516 | the local node (it publishes to itself) |
| CO:653 | `null` (`joinLeaderInTerm` while already a candidate) |
| CO:777 | `null` (`becomeCandidate`) |
| CO:801 | the local node (`becomeLeader`) |
| CO:839 | the leader node (`becomeFollower`) |
| CO:1157 | `null` (`setInitialConfiguration`) |

All six match the docstring.

## Declaration 5: `handlePreVoteRequest`

It takes $\mathit{healthy} \in \mathrm{Bool}$, a collector state $st$ and a request $req$, and returns either an error string or a `PreVoteResponse`. The cases, in order:

1. If $\mathit{healthy} = \mathrm{false}$: error "rejecting on unhealthy node".
2. Otherwise, if $st.\mathrm{leader} = \text{none}$: success with $st.\mathrm{response}$.
3. Otherwise $st.\mathrm{leader} = \text{some } l$:
   - if $l = req.\mathrm{sourceNode}$ (same id **and** same flag): success with $st.\mathrm{response}$;
   - else: error "rejecting as there is already a leader".

Health is checked before the leader. On success the result is always the stored $st.\mathrm{response}$, whatever the request. $req.\mathrm{currentTerm}$ is never read.

*Source check:* PVC:133–163 does the following in order:
- calls `updateMaxTermSeen.accept(request.getCurrentTerm())`;
- asserts the state is non-null;
- throws `NodeHealthCheckFailureException` if the status is `UNHEALTHY`;
- returns `response` if `leader == null`;
- returns `response` if `leader.equals(request.getSourceNode())`;
- throws "there is already a leader" otherwise.

The order of the guards **matches**. Three differences:
- The `updateMaxTermSeen` side effect is omitted, as the docstrings say.
- Leader equality is by (id, role) instead of Java's ephemeral-id `equals`, as the module docstring says.
- Health is a Boolean, read as "status is not `UNHEALTHY`". `StatusInfo.java` is not in the local checkout, so I could not confirm that the Java status has only two values.

## Declaration 6: `PreVotingRound V`

This is a structure with five fields:
- $\mathrm{clusterState}$: a cluster state;
- $\mathrm{localNode}$: a discovery node;
- $\mathrm{preVotesReceived}$: a list of pairs (sender, response);
- $\mathrm{electionStarted}$: a Boolean;
- $\mathrm{isClosed}$: a Boolean.

No equality instance is derived. The type itself imposes nothing:
- The list may contain several entries for the same sender. The docstring's "at most one entry per sender" is not a property of the type. It is a property of the rounds the transition functions produce, and it is the second conjunct of `round_entries`.
- $\mathrm{localNode}$ is unrelated to $\mathrm{clusterState}$.
- $\mathrm{electionStarted}$ may be true with no quorum at all.

*Source check:* PVC:175–300, the inner class `PreVotingRound`, has these fields: a concurrent map `preVotesReceived` keyed by `DiscoveryNode`, an `AtomicBoolean electionStarted`, a `PreVoteRequest preVoteRequest`, a `ClusterState clusterState` and an `AtomicBoolean isClosed`. The local node is not a field. It is read as `clusterState.nodes().getLocalNode()` (PVC:244 and 260). The request (with its term, PVC:112 and 184) is not represented. Java's request source is `transportService.getLocalNode()` (PVC:184), a different expression from the quorum's local node. This model has no request inside the round at all.

## Declaration 7: `PreVotingRound.start`

$$\mathrm{start}(s, n) = \langle s,\ n,\ [\,],\ \mathrm{false},\ \mathrm{false}\rangle.$$
The round has cluster state $s$, local node $n$, no pre-votes, no election started, and is not closed. No relation between $s$ and $n$ is required.

*Source check:* `PreVoteCollector.start` (PVC:111–115) builds a `PreVotingRound(clusterState, state.v2().getCurrentTerm())` and broadcasts requests. The broadcast is not modelled. The Coordinator passes the last accepted state (CO:1608) and the discovered nodes, which include the local node (CO:1312–1317). This confirms the module docstring's "including itself".

## Declaration 8: `PreVotingRound.votes`

$$\mathrm{votes}(r) = \mathrm{foldr}\big((p, v) \mapsto \mathrm{addVote}(v, p.1).1,\ \mathrm{empty},\ r.\mathrm{preVotesReceived}\big).$$

The entries are processed from the end of the list (the oldest) to the front (the most recent). Each sender's id is added if the sender is cluster-manager-eligible and the id is not yet present. The result is a duplicate-free list: the ids of the eligible senders. The responses in the entries are ignored completely.

Examples:
- Entries from $\langle 5,\mathrm{true}\rangle$ and $\langle 5,\mathrm{false}\rangle$ give the single vote $5$.
- An entry from $\langle 5,\mathrm{false}\rangle$ alone gives no vote.

I checked both by evaluation.

*Source check:* PVC:242–257 builds a fresh `VoteCollection` and calls `addJoinVote(new Join(node, localNode, …))` for every map entry. `addJoinVote` (CoordinationState.java:759–765) calls `addVote(join.getSourceNode())`. `addVote` (CoordinationState.java:755–757) is `isClusterManagerNode() && nodes.put(id, node) == null`, keyed by node id. **Matches** in which ids are counted. Java also records the joins, with the response's term, accepted term and version, which a plugin strategy could read. Here they are dropped.

## Declaration 9: `isElectionQuorumFor`

For a strategy $es$, a node $n$, naturals $t$ and $a$, an integer $w$, configurations $C_c$ and $C_a$, and a vote collection $v$:
$$\mathrm{isElectionQuorumFor}(es, n, t, a, w, C_c, C_a, v) = \mathrm{isQuorum}(v, C_c) \wedge \mathrm{isQuorum}(v, C_a) \wedge \mathrm{extra}_{es}(n, t, a, w, C_c, C_a, v).$$

*Source check:* ElectionStrategy.java:68–88 has the final method `isElectionQuorum`, which is exactly `joinVotes.isQuorum(lastCommitted) && joinVotes.isQuorum(lastAccepted) && satisfiesAdditionalQuorumConstraints(…all seven arguments…)`. **Matches.**

## Declaration 10: `PreVotingRound.handlePreVoteResponse`

It takes $es$, a "local response" $lr$, a round $r$, a response $resp$ and a sender. It returns a triple: (new round, start flag, max-term argument), where the last component is "none" or "some $t$". Write $s = r.\mathrm{clusterState}$. The cases, in order:

1. **Closed.** If $r.\mathrm{isClosed}$: the result is $(r, \mathrm{false}, \text{none})$.
2. **Fresher.** If $resp.\mathrm{lastAcceptedTerm} > s.\mathrm{term}$, or $resp.\mathrm{lastAcceptedTerm} = s.\mathrm{term}$ and $resp.\mathrm{lastAcceptedVersion} > \mathrm{vomv}(s)$: the result is $(r, \mathrm{false}, \text{some } resp.\mathrm{currentTerm})$. The response is dropped.
3. **Otherwise.** Let $r_1$ be $r$ with
   $$\mathrm{preVotesReceived} := (\mathit{sender}, resp) :: [\,p \in r.\mathrm{preVotesReceived} \mid p.1 \neq \mathit{sender}\,].$$
   Any earlier entry from a sender *equal* to this one (same id and same flag) is removed, and the new entry is put in front. Let
   $$Q = \mathrm{isElectionQuorumFor}(es,\ r.\mathrm{localNode},\ lr.\mathrm{currentTerm},\ lr.\mathrm{lastAcceptedTerm},\ lr.\mathrm{lastAcceptedVersion},\ s.\mathrm{committed},\ s.\mathrm{accepted},\ \mathrm{votes}(r_1)).$$
   - (a) If $Q$ is false: $(r_1, \mathrm{false}, \text{some } resp.\mathrm{currentTerm})$.
   - (b) Else if $r_1.\mathrm{electionStarted}$ (which equals $r.\mathrm{electionStarted}$): $(r_1, \mathrm{false}, \text{some } resp.\mathrm{currentTerm})$.
   - (c) Else: $(r_1 \text{ with } \mathrm{electionStarted} := \mathrm{true},\ \mathrm{true},\ \text{some } resp.\mathrm{currentTerm})$.

Consequences that can be read off:
- The start flag is true only in case 3(c).
- The third component is "none" exactly in the closed case.
- The round's cluster state, local node and closed flag never change.
- The entry is stored even when the sender is not cluster-manager-eligible. Such a sender then contributes no vote.
- $lr$ enters only as the strategy's term and version arguments, so under the default strategy it is irrelevant.

I checked by evaluation that a fresher response leaves the list unchanged and still reports its current term, and that a closed round reports "none".

*Source check:* PVC:225–279 does the following in order:
- returns if closed (PVC:226–229);
- calls `updateMaxTermSeen.accept(response.getCurrentTerm())` (PVC:231);
- returns on the fresher test (PVC:233–238);
- calls `preVotesReceived.put(sender, response)` (PVC:240);
- rebuilds the votes;
- tests `electionStrategy.isElectionQuorum(localNode, localPreVoteResponse.getCurrentTerm(), …getLastAcceptedTerm(), …getLastAcceptedVersion(), lastCommitted, lastAccepted, voteCollection)`, where `localPreVoteResponse = getPreVoteResponse()` is the collector's current state (PVC:245);
- does `electionStarted.compareAndSet(false, true)` and calls `startElection.run()`.

**Matches**, including that the max-term argument is reported in the fresher case. Java's map `put` replaces by ephemeral-id equality. The filter here removes by (id, role) equality, as the module docstring says.

## Declaration 11: `PreVotingRound.close`

$\mathrm{close}(r)$ is $r$ with $\mathrm{isClosed} := \mathrm{true}$. It is idempotent here.

*Source check:* PVC:296–299 does `isClosed.compareAndSet(false, true)` and asserts that it was not already closed. The assertion is not modelled.

## Declaration 12: `NoFresher`

For a response $resp$ and a cluster state $s$, $\mathrm{NoFresher}(resp, s)$ is the proposition
$$resp.\mathrm{lastAcceptedTerm} < s.\mathrm{term} \;\vee\; \big(resp.\mathrm{lastAcceptedTerm} = s.\mathrm{term} \wedge resp.\mathrm{lastAcceptedVersion} \le \mathrm{vomv}(s)\big).$$
This is lexicographic $\le$ of $(\text{term}, \text{version})$ against $(s.\mathrm{term}, \mathrm{vomv}(s))$. It is exactly the negation of the "fresher" guard of Declaration 10, case 2.

*Source check:* the docstring cites PVC:232–238. The test is at PVC:233–238 (232 is blank). **Matches.**

## Declaration 13: `RoundReachable`

Fix a strategy $es$ and an arbitrary predicate $\mathit{Delivered}(\mathit{sender}, resp)$ on (discovery node, response) pairs. $\mathrm{RoundReachable}_{es,\mathit{Delivered}}$ is the least predicate on rounds that is closed under three rules:
- **start:** for every cluster state $s$ and node $n$, $\mathrm{start}(s, n)$ is reachable;
- **handle:** if $r$ is reachable and $\mathit{Delivered}(\mathit{sender}, resp)$ holds, then for **every** $lr$, the first component of $\mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender})$ is reachable;
- **close:** if $r$ is reachable, so is $\mathrm{close}(r)$.

Consequences of this definition:
- $\mathit{Delivered}$ is one fixed predicate for the whole run. It does not depend on time or on the round.
- The local response $lr$ is chosen freely at each step.
- A sender can deliver any number of times, with different responses each time. Senders need not be among any requested nodes.
- Handle and close steps interleave freely. A handle step after close is a no-op, and close can be repeated.
- The start state $s$ and the local node $n$ are arbitrary and unrelated to each other.
- Along any derivation the round's cluster state and local node stay those given at start.

The docstring says "started over its accepted state". Nothing in the term makes $s$ anyone's accepted state.

## Declaration 14: `handleJoins`

$$\mathrm{handleJoins}(es, cs, js) = \mathrm{foldl}\big(\lambda\, cs\, j.\ \text{if } \mathrm{handleJoin}(es, cs, j) = \text{success}(cs', \_) \text{ then } cs' \text{ else } cs,\ \ cs,\ js\big).$$

The joins are applied from left to right, each to the state the previous one produced. A rejected join leaves the state unchanged, and the "added" Boolean is discarded. A join whose term is above the current term is simply rejected by guard 1 of `handleJoin`. Nothing moves the state to that term. Nothing checks the joins' target node.

*Source check:* `Coordinator.handleJoin` (CO:1267–1287) first calls `ensureTermAtLeast(…, join.getTerm())`, which only matters for a higher term (CO:1269). It then calls `CoordinationState.handleJoin` either through `handleJoinIgnoringExceptions` (CO:1292–1299) when the election is already won, or directly. In `CoordinationState.handleJoin` (CoordinationState.java:264–339) every rejection throws before the first mutation (the throws are at lines 269–317; the vote is added at line 320). So "a rejected join leaves the state unchanged" is **correct**. Java asserts `join.targetMatches(localNode)` (line 265); that assertion is not modelled. The docstring restricts the claim to joins whose term is not above the current term. The definition itself imposes no such restriction.

## Declaration 15: `startElectionTerm`

$$\mathrm{startElectionTerm}(t_c, t_m) = \max(t_c, t_m) + 1.$$

*Source check:* CO:593 builds `new StartJoinRequest(getLocalNode(), Math.max(getCurrentTerm(), maxTermSeen) + 1)`. **Matches.** Java's guards (`mode == CANDIDATE` and `localNodeMayWinElection`, CO:587–591) and the sending to discovered non-Zen1 nodes (CO:595–599) are not part of this definition.

## Declaration 16: `nodeMayWinElection`

For a cluster state $s$, a list of node ids $\mathit{excluded}$ and a node id $n$:
$$\mathrm{nodeMayWinElection}(s, \mathit{excluded}, n) = (n \in s.\mathrm{committed}.\mathrm{ids}) \vee (n \in s.\mathrm{accepted}.\mathrm{ids}) \vee (n \notin \mathit{excluded}).$$
The exclusions are a separate argument, unrelated to $s$. **No theorem of this mission uses this definition.**

*Source check:* CO:628–633 matches, with `getVotingConfigExclusions().stream().noneMatch(…)` as $n \notin \mathit{excluded}$.

## Declaration 17: `SchedulerSettings`

This is a structure with four natural-number fields: $\mathrm{initialTimeout}$, $\mathrm{backoffTime}$, $\mathrm{maxTimeout}$ and $\mathrm{duration}$. The docstring says they are milliseconds. The type carries no unit and no bounds.

*Source check:* the setting keys (ESF:66–69) are `cluster.election.initial_timeout`, `back_off_time`, `max_timeout` and `duration`. Their defaults and bounds (ESF:85–115) are:

| Setting | Default | Range |
|---|---|---|
| initial_timeout | 100 ms | 1 ms – 10 s |
| back_off_time | 100 ms | 1 ms – 60 s |
| max_timeout | 10 s | 200 ms – 300 s |
| duration | 500 ms | 1 ms – 300 s |

These match the docstring. Java reads them as `TimeValue.millis()`.

## Declaration 18: `SchedulerSettings.Valid`

$\mathrm{Valid}(s)$ is the conjunction:
- $1 \le \mathrm{initialTimeout} \le 10000$;
- $1 \le \mathrm{backoffTime} \le 60000$;
- $200 \le \mathrm{maxTimeout} \le 300000$;
- $\mathrm{initialTimeout} \le \mathrm{maxTimeout}$;
- $1 \le \mathrm{duration} \le 300000$.

*Source check:* these are the setting bounds above, plus the constructor check at ESF:133–143 (it throws if `maxTimeout.millis() < initialTimeout.millis()`). **Matches.** `Setting.java` is not in the local checkout, so I could not see how the bounds are checked for sub-millisecond `TimeValue`s.

## Declaration 19: `SchedulerSettings.default`

$\langle 100, 100, 10000, 500\rangle$, that is: initialTimeout $100$, backoffTime $100$, maxTimeout $10000$, duration $500$. These match the Java defaults, and the value satisfies $\mathrm{Valid}$. **No theorem of this mission uses it.**

## Declaration 20: `maxDelay`

$$\mathrm{maxDelay}(s, k) = \min\big(s.\mathrm{maxTimeout},\ s.\mathrm{initialTimeout} + k \cdot s.\mathrm{backoffTime}\big),$$
in unbounded natural-number arithmetic, so there is no overflow. With the defaults it is $100 + 100k$ up to $k = 99$, where it first reaches $10000$; I checked this by evaluation. Without $\mathrm{Valid}$ it can be $0$, for example with initialTimeout $0$ and backoffTime $0$.

*Source check:* ESF:203 is `Math.min(maxTimeout.millis(), initialTimeout.millis() + thisAttempt * backoffTime.millis())`, where `thisAttempt` counts from $0$ (ESF:201). **Matches.** The Java comment there notes that overflow would take "over a million years".

## Declaration 21: `nonNegative`

For any integer $n$:
$$\mathrm{nonNegative}(n) = \begin{cases} 0 & \text{if } n = -2^{63},\\ |n| & \text{otherwise.}\end{cases}$$
`-2 ^ 63` parses as $-(2^{63}) = -9223372036854775808$, which is `Long.MIN_VALUE`. I confirmed the parse with `pp.parens`; since $63$ is odd, $(-2)^{63}$ would give the same value anyway.

The domain is all of $\mathbb{Z}$, not only Java's long range. Outside $[-2^{63}, 2^{63})$ the function returns $|n|$, for example $\mathrm{nonNegative}(-2^{63}-1) = 2^{63}+1$. No Java long gives such a value. The docstring states the long range, but the definition does not restrict to it.

*Source check:* ESF:159–161 is `n == Long.MIN_VALUE ? 0 : Math.abs(n)`. **Matches** on longs.

## Declaration 22: `toPositiveLongAtMost`

For an integer $x$ and $u \in \mathbb{N}$:
$$\mathrm{toPositiveLongAtMost}(x, u) = \big(\mathrm{nonNegative}(x) \bmod u\big) + 1,$$
with natural-number $\bmod$.
- For $u \ge 1$ the result is in $[1, u]$.
- For $u = 0$, Lean's $\bmod 0$ returns the dividend, so the result is $\mathrm{nonNegative}(x) + 1$. Java asserts `0 < upperBound`, and Java's `%` by zero would throw. The definition leaves this case defined but meaningless.

*Source check:* ESF:169–172. **Matches** for $u > 0$.

## Declaration 23: `attemptDelay`

For settings $s$, an attempt index $k$, an integer $x$ (the random long) and a grace period $g \in \mathbb{N}$:
$$\mathrm{attemptDelay}(s, k, x, g) = \mathrm{toPositiveLongAtMost}\big(x, \mathrm{maxDelay}(s, k)\big) + g.$$

The docstring says $g$ is $0$ for the first attempt and $s.\mathrm{duration}$ for later ones. The definition takes $g$ as a free argument, and nothing ties it to $0$ or to $s.\mathrm{duration}$. In fact $s.\mathrm{duration}$ is read by no definition of the file except $\mathrm{Valid}$.

*Source check:* ESF:195–204 computes `delayMillis = toPositiveLongAtMost(random.nextLong(), maxDelayMillis) + gracePeriod.millis()`. Later attempts are rescheduled with `scheduleNextElection(duration, …)` (ESF:218). The first grace period is `TimeValue.ZERO` (CO:1574). **Matches.**

---

## Remarks on the docstrings

- **Module docstring, "Both handlers first raise the Coordinator's `maxTermSeen`."** `handlePreVoteResponse` tests the closed flag first and raises the term only if the round is open. Its own docstring and code say so correctly; the module sentence is loose.
- **Module docstring, "the leader moves to that term and starts an election itself (CO:565-577)."** In Java this happens only when no publication is in progress; otherwise the term bump is deferred (CO:567–568). If the bump fails, the node becomes a candidate (CO:574–576). The docstring places this effect outside the functions, and no definition models it.
- **Module docstring on node equality.** It says the Lean and Java comparisons "agree except between two incarnations of the same node". Two incarnations with *different* roles are distinct under both comparisons. The real disagreement is between two incarnations with the same id and role.
- **`PreVotingRound`, "at most one entry per sender."** This is not a type invariant (see Declaration 6). "Sender" here means a discovery-node value, that is, an (id, role) pair, so two entries may share an id. I checked by evaluation: senders $\langle 5,\mathrm{true}\rangle$ and $\langle 5,\mathrm{false}\rangle$ both stay in the list.
- **`RoundReachable`, "started over its accepted state."** The start rule accepts any cluster state.
- **`nonNegative`, "on a Java `long`."** The definition is total on $\mathbb{Z}$.
- **`attemptDelay`, the grace-period description.** This describes how Java calls the function. The grace period is a free parameter here.
- **Unused declarations.** No theorem of this mission uses `nodeMayWinElection` or `SchedulerSettings.default`.
