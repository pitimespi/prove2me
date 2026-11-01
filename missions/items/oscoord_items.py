SRC = ("OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (constructor lines 84-106, isElectionQuorum 144-154, "
       "isPublishQuorum 156-158, setInitialState 180-204, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, "
       "handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573, invariant 601-611, "
       "PersistedState.markLastAcceptedStateAsCommitted 703-728, commitVotingConfiguration 730-740, VoteCollection 750-814), "
       "server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java: "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java#L64-L815; "
       "CoordinationMetadata.VotingConfiguration (lines 383-449, hasQuorum 405-409): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationMetadata.java#L383-L449; "
       "ElectionStrategy (DEFAULT_INSTANCE lines 46-59, isElectionQuorum 68-88): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; "
       "ClusterState.getVersionOrMetadataVersion (lines 239-244): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/ClusterState.java#L239-L244; "
       "Coordinator.ZEN1_BWC_TERM (line 134): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java#L134; "
       "the messages StartJoinRequest.java, Join.java, PublishRequest.java, PublishResponse.java, ApplyCommitRequest.java in the same directory; "
       "test vectors from server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java "
       "(https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java) "
       "and CoordinationMetadataTests.java (testVotingConfiguration)")
TAGS = ["opensearch", "elasticsearch", "consensus", "cluster-coordination", "zen2", "raft", "paxos", "coordination-state",
        "quorum", "leader-election", "formal-verification"]

DEFINITION = {
    "definition_name": "OpenSearchCoordination",
    "definition_title": "OpenSearch CoordinationState: voting configurations, vote collections, the reduced cluster state, and the seven handlers of the per-node consensus state machine",
    "natural_language_statement": r"""A transcription of `org.opensearch.cluster.coordination.CoordinationState` at OpenSearch revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, the per-node state machine of OpenSearch's cluster coordination ("Zen2"), with the parts of `VotingConfiguration`, `ElectionStrategy`, `ClusterState` and the message classes it reads. Line numbers below are those of `CoordinationState.java` unless stated.

**Nodes.** **`NodeId`** — a natural number (Java: the node id string). **`DiscoveryNode`** — a node id and whether the node has the cluster-manager (master-eligible) role, `isClusterManagerNode`. **`ZEN1_BWC_TERM`** — the term `0` (`Coordinator.java:134`): the term of the states a node holds before the first election, and of the states an Elasticsearch 6.x (Zen1) cluster-manager publishes during a rolling upgrade.

**Voting configurations.** **`VotingConfiguration`** — a list of node ids that is strictly increasing, so that two configurations are equal exactly when they have the same members (Java compares the sets of ids). **`EMPTY_CONFIG`** — the empty configuration; **`isEmpty`**. **`hasQuorum c votes`** — the number of members of `c` that occur in the list `votes`, doubled, exceeds the number of members of `c` (`CoordinationMetadata.java:405-409`); an empty configuration has no quorum.

**Vote collections.** **`VoteCollection`** — the list of ids of the nodes whose votes were added, most recent first; **`empty`**. **`addVote v n`** (755-757) — if `n` has the cluster-manager role and its id is not yet present, the collection with `n.id` added and `true`; otherwise `v` unchanged and `false`. **`isQuorum v c`** — `c.hasQuorum` of the ids; **`containsVoteFor v n`** — `n.id` is present; **`isEmpty`**.

**Cluster states.** **`ClusterState V`** — the fields `CoordinationState` reads or writes: `term` (natural number), `version` and `metadataVersion` (integers), `lastCommittedConfiguration`, `lastAcceptedConfiguration`, `clusterManagerNode` (the elected cluster-manager, identified by its ephemeral id, or `none` for Java `null`), `clusterUUIDKnown`, `clusterUUIDCommitted`, and an opaque payload `value : V` standing for everything else. **`versionOrMetadataVersion s`** — the metadata version when `s.term = 0`, otherwise the version (`ClusterState.java:239-244`). **`markCommitted s`** (703-740) — if the accepted configuration differs from the committed one, the committed configuration becomes the accepted one; then, if the cluster UUID is known and not committed, it is marked committed.

**Messages.** **`StartJoinRequest`** (source node, term); **`Join`** (source node, target node, term, the voter's last accepted term, and its last accepted version or metadata version); **`PublishRequest V`** (the accepted state); **`PublishResponse`** (term, version); **`ApplyCommitRequest`** (source node, term, version).

**Election strategies.** **`ElectionStrategy`** — a function `satisfiesAdditionalQuorumConstraints` of the local node, the current term, the last accepted term and version, the last committed and last accepted configurations and the vote collection, returning a Boolean (the plugin extension point; `isElectionQuorum` itself is final in Java). **`DEFAULT_INSTANCE`** — the constant `true`. **`Monotone es`** — for all arguments, if every id of `v` is an id of `w` and the constraint holds for `v`, it holds for `w`.

**The state.** **`CoordinationState V`** — the local node; the persisted current term (natural number) and last accepted cluster state; and the transient `joinVotes`, `startedJoinSinceLastReboot`, `electionWon`, `lastPublishedVersion` (integer), `lastPublishedConfiguration`, `publishVotes`. **`init n t s`** (84-106) — node `n` over the persisted term `t` and accepted state `s`: empty join and publish votes, `startedJoinSinceLastReboot = false`, `electionWon = false`, `lastPublishedVersion = 0`, `lastPublishedConfiguration` the accepted configuration of `s`. The accessors **`lastAcceptedTerm`**, **`lastAcceptedVersion`**, **`lastAcceptedVersionOrMetadataVersion`**, **`lastCommittedConfiguration`**, **`lastAcceptedConfiguration`** read the last accepted state. **`isElectionQuorum es cs votes`** (144-154) — `votes` is a quorum of the last committed configuration and of the last accepted configuration, and the strategy's constraint holds for the local node, current term, last accepted term and version, the two configurations and `votes`. **`isPublishQuorum cs votes`** (156-158) — a quorum of the last committed configuration and of `lastPublishedConfiguration`.

**The handlers**, each returning a rejection (`.error` with a message) or the new state, paired with its output for the five that have one (all but `setInitialState` and `handleCommit`), checking the Java conditions in the Java order:

- **`setInitialState cs s`** (180-204) — rejects if the last accepted configuration is nonempty; otherwise the last accepted state becomes `s`. **`initialStateContract cs s`** — the method's assertions (190-201): last accepted term 0, empty committed configuration, `lastPublishedVersion = 0`, empty `lastPublishedConfiguration`, election not won, empty join and publish votes, `s.term = 0`, `s.version` equal to the last accepted version, and both configurations of `s` nonempty.
- **`handleStartJoin cs req`** (213-255) — rejects if `req.term ≤ currentTerm`; otherwise sets the current term to `req.term`, `lastPublishedVersion` to 0, `lastPublishedConfiguration` to the last accepted configuration, `startedJoinSinceLastReboot` to true, `electionWon` to false, empties both vote collections, and returns the `Join` from the local node to `req.sourceNode` in term `req.term` with the last accepted term and version-or-metadata-version.
- **`handleJoin es cs j`** (264-339) — rejects, in order, if `j.term ≠ currentTerm`; if no start-join was handled since the last restart; if `j.lastAcceptedTerm > lastAcceptedTerm`; if the terms are equal and `j.lastAcceptedVersion > lastAcceptedVersionOrMetadataVersion`; if the last accepted configuration is empty. Otherwise adds the vote of `j.sourceNode`, sets `electionWon` to `isElectionQuorum es cs` of the new votes, sets `lastPublishedVersion` to the last accepted version if the election has just been won, and returns whether the vote was new.
- **`handleClientValue cs s`** (348-407) — rejects if the election is not won; if `lastPublishedVersion ≠ lastAcceptedVersion`; if `s.term ≠ currentTerm`; if `s.version ≤ lastPublishedVersion`; if `s` changes the accepted configuration while the committed configuration differs from the accepted one; if the join votes are not a quorum of `s`'s accepted configuration. Otherwise sets `lastPublishedVersion` to `s.version`, `lastPublishedConfiguration` to `s`'s accepted configuration, empties the publish votes and returns the `PublishRequest` of `s`. **`clientValueContract cs s`** — the assertion of 397-398: `s` has the node's last committed configuration.
- **`handlePublishRequest cs req`** (416-460) — for the incoming state `s`: rejects if `s.term ≠ currentTerm`; if `s.term` equals the last accepted term and `s.version ≤ lastAcceptedVersion`, rejects unless `s.term = 0`, `s` names a cluster-manager, and the last accepted state names none or a different one (the Zen1 compatibility branch; a term-0 state naming no cluster-manager is rejected there, Java's `NullPointerException`); otherwise the last accepted state becomes `s` and the response carries `s.term` and `s.version`.
- **`handlePublishResponse cs src r`** (471-515) — rejects if the election is not won; if `r.term ≠ currentTerm`; if `r.version ≠ lastPublishedVersion`. Otherwise adds the vote of `src` to the publish votes, and returns the `ApplyCommitRequest` (local node, `r.term`, `r.version`) if the new votes are a publish quorum, nothing otherwise.
- **`handleCommit cs c`** (523-573) — rejects if `c.term ≠ currentTerm`, if `c.term ≠ lastAcceptedTerm`, or if `c.version ≠ lastAcceptedVersion`; otherwise replaces the last accepted state by `markCommitted` of it.

**`javaInvariant es cs`** — the five assertions of `invariant()` (601-611): the last accepted term is at most the current term; `electionWon` equals `isElectionQuorum es cs joinVotes`; if the election is won, `lastPublishedVersion ≥ lastAcceptedVersion`, otherwise `lastPublishedVersion = 0`; a won election implies `startedJoinSinceLastReboot`; the publish votes are empty or the election is won.

**Formalization Note.** Node ids are naturals (only their equality is used); two `DiscoveryNode`s are equal when their ids and roles are, whereas Java compares ephemeral ids (no handler compares nodes), and `clusterManagerNode` holds an ephemeral id, a natural number unrelated to the node ids. The election strategy is an argument of `isElectionQuorum`, `handleJoin` and `javaInvariant` rather than a field of the state (Java: a `final` field); each theorem uses a single strategy. Terms are naturals (Java `long`s that are never negative: a fresh node's persisted term is 0, and among the handlers only `handleStartJoin` changes the current term, upwards); `init` takes the persisted term as a parameter, so a state may be in any term. Versions are integers (Java `long`; overflow is not modelled). A cluster state keeps only the fields above; the payload is a type parameter. Vote collections keep only voter ids: Java also records the `Join`s, which only tests read, and Java's `equals` (used only by tests) compares the map of voters and the recorded joins, whereas `=` here compares the lists of ids, including their order (the order in which votes were added) and multiplicity; no handler compares vote collections. The remote cluster-state store (the REMOTE persisted state) is omitted: the handlers read it only to decide whether to write it (616-642; the write in `handlePublishResponse`, `handlePreCommit` at 510 and 593-599, is gated by the `isRemoteStateEnabled` setting), every value they compute comes from the LOCAL persisted state, and a failed remote write makes the Java method throw after its local effects, where the transcription returns the result: the Java run is then the transcription's run with that output lost, which a cluster model whose messages may be lost includes. Java `assert`s are disabled in production; the handlers do not check them, and the asserted preconditions of `setInitialState` and `handleClientValue` are stated separately as `initialStateContract` and `clientValueContract`, which no other definition and no theorem of this mission uses. Not represented: the assertion that a join targets the local node (265), the assertion of `markLastAcceptedStateAsCommitted` that a state with an unknown cluster UUID is committed only in term 0 (708-710), and the assertions of the `Join` and `PublishResponse` constructors that their versions are non-negative (versions here are unbounded integers; terms are naturals). Rejection messages are fixed strings containing the substrings OpenSearch's tests match. The file has no imports (Lean core only).""",
}

THEOREMS = {
"OpenSearchCoordination.quorum_intersect": dict(
    title="Two quorums of one voting configuration share a member",
    nl=r"""For every voting configuration `c` and lists of node ids `a` and `b`: if `c.hasQuorum a = true` and `c.hasQuorum b = true`, then some node id `x` is a member of `c` (`x ∈ c.nodeIds`) and occurs in both `a` and `b`.

Here `c.hasQuorum votes` holds when the number of members of `c` occurring in `votes`, doubled, exceeds the number of members of `c`: a strict majority of the configuration. This is the intersection property every safety argument of the protocol rests on: two elections, or an election and a commit, decided by quorums of the same configuration have a voter in common.""",
    ms=("Quorum intersection", "Count the members of the configuration in each vote list: two counts each above half of the configuration's size force a member counted in both.")),
"OpenSearchCoordination.quorum_mono": dict(
    title="A superset of a quorum is a quorum",
    nl=r"""For every voting configuration `c` and lists of node ids `a` and `b` such that every element of `a` occurs in `b`: if `c.hasQuorum a = true` then `c.hasQuorum b = true`. Adding votes never destroys a quorum.""",
    ms=None),
"OpenSearchCoordination.empty_no_quorum": dict(
    title="The empty voting configuration has no quorum",
    nl=r"""For every list of node ids `a`: `VotingConfiguration.EMPTY_CONFIG.hasQuorum a = false`, since $0 \cdot 2 > 0$ fails. With the definitions, it follows that `isElectionQuorum` fails at a node whose last committed or last accepted configuration is empty, and `isPublishQuorum` fails at a node whose last committed configuration or `lastPublishedConfiguration` is empty: both require a quorum of each of two configurations.""",
    ms=None),
"OpenSearchCoordination.no_votes_no_quorum": dict(
    title="An empty vote collection is a quorum of no configuration",
    nl=r"""For every voting configuration `c`: `VoteCollection.empty.isQuorum c = false`. No member of `c` occurs among no votes, and $0 \cdot 2$ never exceeds the number of members of `c`, including when `c` is empty.""",
    ms=None),
"OpenSearchCoordination.addVote_eligible": dict(
    title="Only votes of cluster-manager-eligible nodes are counted",
    nl=r"""For every vote collection `v`, node `n` and node id `x`: `x` is among the ids of `(v.addVote n).1` iff `x` is among the ids of `v`, or `x = n.id` and `n.isClusterManagerNode = true`.

`addVote` adds exactly the id of a node with the cluster-manager role and nothing else; the vote of a node without the role, or a vote already present, leaves the set of voters unchanged.""",
    ms=None),
"OpenSearchCoordination.handleStartJoin_spec": dict(
    title="handleStartJoin succeeds exactly when the term increases; it moves to that term and votes for the requester",
    nl=r"""For every coordination state `cs`, start-join request `req`, state `cs'` and join `j`: `cs.handleStartJoin req = .ok (cs', j)` holds iff all of the following hold:

- `cs.currentTerm < req.term`, and `cs'.currentTerm = req.term`;
- `cs'` has the last accepted state and the local node of `cs`;
- `cs'.startedJoinSinceLastReboot = true` and `cs'.electionWon = false`;
- the join votes and the publish votes of `cs'` are `VoteCollection.empty`;
- `cs'.lastPublishedVersion = 0` and `cs'.lastPublishedConfiguration = cs.lastAcceptedConfiguration`;
- `j` is the join from `cs.localNode` to `req.sourceNode` in term `req.term`, carrying `cs.lastAcceptedTerm` and `cs.lastAcceptedVersionOrMetadataVersion` (the last accepted state's version, or its metadata version if its term is 0).

The conditions on `cs'` fix all nine of its fields, so the result of a successful call is determined; a request whose term is not above the current term is rejected.""",
    ms=("handleStartJoin characterized", "Both directions: the term guard is the only rejection, and the successful result is the record update together with the join.")),
"OpenSearchCoordination.handlePublishRequest_spec": dict(
    title="handlePublishRequest accepts only a strictly newer state of the current term, Zen1 compatibility aside",
    nl=r"""Let `cs` be a coordination state with `cs.lastAcceptedTerm ≤ cs.currentTerm`, and suppose `cs.handlePublishRequest req = .ok (cs', resp)`. Then:

- `cs'.lastAcceptedState = req.acceptedState` and `req.acceptedState.term = cs.currentTerm`;
- `cs'` has the current term and the local node of `cs`;
- `resp` carries the term and the version of `req.acceptedState`;
- the accepted state is strictly newer than the old one in the lexicographic (term, version) order — `cs.lastAcceptedTerm < req.acceptedState.term`, or the terms are equal and `cs.lastAcceptedVersion < req.acceptedState.version` — or its term is `ZEN1_BWC_TERM` (0), about which nothing more is stated: this disjunct holds for every term-0 state (the handler accepts a term-0 state that is not newer only in its Zen1 compatibility branch, when that state names a cluster-manager and the last accepted state names none or a different one; the statement does not record this condition);
- the join votes, `electionWon`, `startedJoinSinceLastReboot`, `lastPublishedVersion`, `lastPublishedConfiguration` and the publish votes are those of `cs`.

The hypothesis on `cs` is the first assertion of `invariant()`; without it, a node whose accepted term exceeds its current term would accept a state of a lower term.""",
    ms=("Publication moves the accepted state forward", "Walk the guards; in the accepting branch compare the incoming (term, version) with the accepted one, using that the incoming term is the current term and the accepted term is at most it.")),
"OpenSearchCoordination.handleCommit_spec": dict(
    title="handleCommit only marks the last accepted state committed",
    nl=r"""For every coordination state `cs`, commit request `c` and state `cs'`: if `cs.handleCommit c = .ok cs'` then

- the commit is for the last accepted state in the current term: `c.term = cs.currentTerm`, `c.term = cs.lastAcceptedTerm` and `c.version = cs.lastAcceptedVersion`;
- `cs'` is `cs` with its last accepted state replaced by `cs.lastAcceptedState.markCommitted` (the committed configuration becomes the accepted one, and a known cluster UUID is marked committed);
- in `cs'` the last committed configuration equals the last accepted configuration (the assertion at `CoordinationState.java:572`);
- the last accepted configuration, term, version and payload of `cs'` are those of `cs`.""",
    ms=("handleCommit characterized", "Walk the three guards; unfold `markCommitted` and split its two conditionals.")),
"OpenSearchCoordination.lastAcceptedTerm_le_currentTerm": dict(
    title="Only handleStartJoin changes the current term, and every handler keeps the accepted term at most the current term",
    nl=r"""For every election strategy `es` and coordination state `cs` with `cs.lastAcceptedTerm ≤ cs.currentTerm`, every successful handler call on `cs` — for `setInitialState s`, one with `s.term = 0`, one of the method's asserted preconditions (a conjunct of `initialStateContract`, the only one assumed) — yields a state `cs'` with `cs'.lastAcceptedTerm ≤ cs'.currentTerm`, and moreover:

- `cs.setInitialState s = .ok cs'` with `s.term = 0` leaves the current term unchanged;
- `cs.handleStartJoin r = .ok (cs', j)` strictly increases it: `cs.currentTerm < cs'.currentTerm`;
- `cs.handleJoin es j`, `cs.handleClientValue s`, `cs.handlePublishRequest p`, `cs.handlePublishResponse n r` and `cs.handleCommit c`, when they succeed, leave it unchanged.

So the first assertion of `invariant()`, `getLastAcceptedTerm() <= getCurrentTerm()`, is preserved by one successful call of any handler, and along successful calls on one node that start from a state satisfying it (with term-0 states for `setInitialState`) the current term changes only at `handleStartJoin`, upwards. The statement is about single steps; it does not mention `init`, whose result satisfies the inequality exactly when `s.term ≤ t` (the hypothesis of `init_javaInvariant`).""",
    ms=("Terms only move forward", "Per handler: only `handleStartJoin` writes the current term, upwards; `handlePublishRequest` accepts only states of the current term; `setInitialState` installs a term-0 state; the others keep the accepted term.")),
"OpenSearchCoordination.handleJoin_spec": dict(
    title="handleJoin: which votes are counted, and electionWon recomputed",
    nl=r"""For every election strategy `es`, coordination state `cs`, join `j`, state `cs'` and flag `b`: if `cs.handleJoin es j = .ok (cs', b)` then

- the join is for the current term: `j.term = cs.currentTerm`;
- the node has handled a start-join since its last restart (`cs.startedJoinSinceLastReboot = true`) and has been bootstrapped (`cs.lastAcceptedConfiguration.isEmpty = false`);
- the voter's accepted state is no fresher than the node's: `j.lastAcceptedTerm < cs.lastAcceptedTerm`, or the terms are equal and `j.lastAcceptedVersion ≤ cs.lastAcceptedVersionOrMetadataVersion`;
- the new join votes are `(cs.joinVotes.addVote j.sourceNode).1`, and `b` is `(cs.joinVotes.addVote j.sourceNode).2`, whether the vote was new;
- `cs'.electionWon = cs.isElectionQuorum es cs'.joinVotes`: `electionWon` is recomputed as whether the new votes are a quorum of the last committed and of the last accepted configuration of `cs` and satisfy the strategy's additional constraint (nothing is assumed of `cs` or `es`, so a successful join may also turn `electionWon` from true to false, for instance where `cs.electionWon` disagrees with its votes, or for a strategy that is not monotone; `handleJoin_stays_won` rules this out under its hypotheses);
- the current term, last accepted state, local node, `startedJoinSinceLastReboot`, publish votes and `lastPublishedConfiguration` of `cs'` are those of `cs`;
- `cs'.lastPublishedVersion` is `cs.lastAcceptedVersion` if this join won the election (`cs'.electionWon = true` and `cs.electionWon = false`), and `cs.lastPublishedVersion` otherwise.

The Java assertion that the join targets this node (`CoordinationState.java:265`) is not checked by the transcription and does not appear here.""",
    ms=("handleJoin characterized", "Walk the five guards; then the vote update and the two outcomes of the test whether the election has just been won.")),
"OpenSearchCoordination.default_monotone": dict(
    title="The default election strategy is monotone",
    nl=r"""`ElectionStrategy.DEFAULT_INSTANCE.Monotone`: for all arguments and all vote collections `v` and `w` such that every id of `v` is an id of `w`, if the default strategy's additional constraint holds for `v` then it holds for `w`. The default strategy, the only one in OpenSearch itself, imposes no additional constraint: it is the constant `true`.""",
    ms=None),
"OpenSearchCoordination.handleJoin_stays_won": dict(
    title="A won election stays won (CoordinationState.java:323-324)",
    nl=r"""Let `es` be a monotone election strategy (`es.Monotone`) and `cs` a coordination state whose `electionWon` agrees with the election-quorum status of its join votes, `cs.electionWon = cs.isElectionQuorum es cs.joinVotes` (the second assertion of `invariant()`). If `cs.electionWon = true` and `cs.handleJoin es j = .ok (cs', b)`, then `cs'.electionWon = true`.

This is the assertion `assert !prevElectionWon || electionWon` ("we cannot go from won to not won") in `handleJoin`: a join only adds a vote, a superset of a quorum is a quorum, and a monotone strategy's constraint survives added votes. Java does not require plugin strategies to be monotone; the theorem does.""",
    ms=("We cannot go from won to not won", "Votes only grow under `handleJoin` (`addVote_eligible`); `quorum_mono` for the two configurations and monotonicity for the strategy's constraint.")),
"OpenSearchCoordination.handleClientValue_spec": dict(
    title="handleClientValue publishes only as an elected node, in its term, above the last version, reconfiguring only safely",
    nl=r"""For every coordination state `cs`, cluster state `s`, state `cs'` and publish request `p`: if `cs.handleClientValue s = .ok (cs', p)` then

- `cs.electionWon = true`;
- `cs.lastPublishedVersion = cs.lastAcceptedVersion`: the node has accepted its own last publication;
- `s.term = cs.currentTerm` and `cs.lastAcceptedVersion < s.version` (so the new version is above the last published one);
- `s` keeps the node's last accepted configuration (`s.lastAcceptedConfiguration = cs.lastAcceptedConfiguration`), or no reconfiguration is pending (`cs.lastCommittedConfiguration = cs.lastAcceptedConfiguration`);
- the node's join votes are a quorum of the new accepted configuration: `cs.joinVotes.isQuorum s.lastAcceptedConfiguration = true`;
- `p` is the publish request of `s`, and `cs'` is `cs` with `lastPublishedVersion := s.version`, `lastPublishedConfiguration := s.lastAcceptedConfiguration` and empty publish votes.

The asserted precondition that `s` keeps the node's last committed configuration (`clientValueContract`, `CoordinationState.java:397-398`) is a caller contract and is not part of the statement.""",
    ms=("handleClientValue characterized", "Walk the six guards; the reconfiguration guard gives the disjunction.")),
"OpenSearchCoordination.handlePublishResponse_spec": dict(
    title="handlePublishResponse commits only on a publish quorum of both configurations",
    nl=r"""For every coordination state `cs`, node `src`, publish response `r`, state `cs'` and optional commit `o`: if `cs.handlePublishResponse src r = .ok (cs', o)` then

- `cs.electionWon = true`, `r.term = cs.currentTerm` and `r.version = cs.lastPublishedVersion`;
- `cs'` is `cs` with publish votes `(cs.publishVotes.addVote src).1`;
- if `o = some c`, then `c` is the commit `⟨cs.localNode, cs.currentTerm, cs.lastPublishedVersion⟩` (sent by this node, for its current term and the version being published), and the new publish votes are a quorum of `cs.lastCommittedConfiguration` and of `cs.lastPublishedConfiguration`, the configuration being published.

The statement says when a commit can be emitted; it is one-directional: it does not say that a commit is emitted whenever the new votes are a publish quorum, and it says nothing when `o = none`.""",
    ms=("Commits need two publish quorums", "Walk the three guards; in the committing branch unfold `isPublishQuorum` on the updated state, whose configurations are those of `cs`.")),
"OpenSearchCoordination.init_javaInvariant": dict(
    title="A freshly started node satisfies invariant()",
    nl=r"""For every election strategy `es`, node `n`, term `t` and cluster state `s` with `s.term ≤ t`: `(CoordinationState.init n t s).javaInvariant es`. The constructor, which a restart runs over the persisted current term `t` and last accepted state `s`, yields empty votes, no election and last published version 0, and these satisfy the five assertions of `invariant()` as soon as the persisted accepted term is at most the persisted current term.""",
    ms=None),
"OpenSearchCoordination.handleStartJoin_javaInvariant": dict(
    title="handleStartJoin re-establishes invariant()",
    nl=r"""For every election strategy `es` and coordination state `cs` with `cs.lastAcceptedTerm ≤ cs.currentTerm` (nothing else is assumed): if `cs.handleStartJoin r = .ok (cs', j)` then `cs'.javaInvariant es`. Moving to a higher term discards the votes and the election, which makes the last four assertions of `invariant()` hold whatever held before; the first, assumed of `cs`, survives because the current term grows and the accepted state is unchanged.""",
    ms=None),
"OpenSearchCoordination.javaInvariant_preserved": dict(
    title="invariant() is preserved by handleJoin, handleClientValue and handlePublishResponse",
    nl=r"""For every monotone election strategy `es` and coordination state `cs` with `cs.javaInvariant es`:

- if `cs.handleJoin es j = .ok (cs', b)` then `cs'.javaInvariant es`;
- if `cs.handleClientValue s = .ok (cs', p)` then `cs'.javaInvariant es`;
- if `cs.handlePublishResponse n r = .ok (cs', o)` then `cs'.javaInvariant es`.

`javaInvariant` is the conjunction of the five assertions of `invariant()` (`CoordinationState.java:601-611`). With `init_javaInvariant` and `handleStartJoin_javaInvariant` this accounts for every handler except `handlePublishRequest` (see `javaInvariant_not_local`), `handleCommit` and `setInitialState`, the three that change the configurations the second assertion reads.""",
    ms=None),
"OpenSearchCoordination.javaInvariant_not_local": dict(
    title="invariant() is not preserved by handlePublishRequest in isolation",
    nl=r"""There exist a coordination state `cs` and a publish request `p` (payload type `Unit`) such that `cs` satisfies `javaInvariant` for the default election strategy, `cs.handlePublishRequest p` succeeds with some state `cs'` and response, and `cs'` does not satisfy `javaInvariant` for the default strategy.

In the witness, node 0 is in term 1 with an accepted term-0 state whose configurations are {1, 2, 3}; it holds a join vote of node 4 and has not won an election. It accepts a term-1 state whose configurations are {4}; its join votes are then an election quorum while `electionWon` is false. Whether `invariant()` holds along an execution therefore depends on what the other nodes did: it is a property of the cluster, which the `OpenSearchSafety` mission proves at every cluster-manager-eligible node of its cluster model, assuming compatible bootstrap configurations and the default election strategy (`OpenSearchSafety.javaInvariant_reachable`).""",
    ms=("invariant() is a cluster property", "An explicit counterexample: a node holding a stray vote accepts a publication whose configurations that vote is a quorum of.")),
}
ORDER = ["OpenSearchCoordination." + k for k in ["quorum_intersect", "quorum_mono", "empty_no_quorum", "no_votes_no_quorum",
  "addVote_eligible", "handleStartJoin_spec", "handlePublishRequest_spec", "handleCommit_spec", "lastAcceptedTerm_le_currentTerm",
  "handleJoin_spec", "default_monotone", "handleJoin_stays_won", "handleClientValue_spec", "handlePublishResponse_spec",
  "init_javaInvariant", "handleStartJoin_javaInvariant", "javaInvariant_preserved", "javaInvariant_not_local"]]
