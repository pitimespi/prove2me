# Read-back: `Def_OpenSearchCoordination.lean`

The file has no `import` lines, so it uses only Lean's core library. After a module docstring it declares everything in the namespace `OpenSearchCoordination`. In source order, it declares:

- node and configuration types;
- a vote-collection type with five operations;
- a reduced cluster state with two operations;
- five message structures;
- an election-strategy structure with a default instance and a monotonicity predicate;
- the coordination state with its constructor, five accessors and two quorum tests;
- seven handlers, two "contract" predicates and the Java invariant.

Each declaration is rendered below in that order.

**Notation.** For a Boolean $b$ used as a proposition, "$b$" means $b = \mathrm{true}$. Lean's `Except String α` has two outcomes, written $\mathrm{ok}(x)$ and $\mathrm{error}(m)$ for a message string $m$; no theorem inspects the messages. "$r$ with $f := e$" is a record update that leaves all other fields unchanged.

**Citation check.** The docstrings cite source files at revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`:

- `CS:<line>` is `server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java`.
- `CM:<line>` is `CoordinationMetadata.java` in the same directory.
- `ES:<line>` is `ElectionStrategy.java` in the same directory.
- `CLS:<line>` is `server/src/main/java/org/opensearch/cluster/ClusterState.java`.
- `Coordinator.java:134` is also cited.

The local checkout `/home/user/opensearch-project/OpenSearch` has exactly that `HEAD`. Every cited range delimits the Java member it names: CS:84-106 (the constructor), 144-154, 156-158, 180-204, 190-201, 213-255, 264-339, 348-407, 397-398, 416-460, 471-515, 523-573, 601-611, 703-728, 730-740, 750-814, 755-757, 772-774, 776-778, 780-782 and 798-806; CM:383-449, 385, 405-409 and 433-435; ES:68-88; CLS:239-244; Coordinator.java:134. CS:64-106 runs from the class declaration to the end of the constructor and so covers the fields. CS:616-642 covers the three remote-state helpers (617-642). Each declaration below has its own verdict.

## Module docstring (claims, checked against the code)

1. *"Transcription of the per-node consensus state machine ... `CoordinationState` ... at OpenSearch revision `b2a54ba…`."* The revision matches the local checkout.
2. *"Node ids are `Nat` (Java: `String`); only equality is used."* In the file, ids are compared by equality and list membership. The order `<` on ids appears only in the sortedness proof field of `VotingConfiguration`.
3. *"Terms are `Nat`: the persisted term starts at `0` and only `handleStartJoin` changes it, to a strictly larger value."* `handleStartJoin` is the only handler that writes `currentTerm`, and it writes only a strictly larger value. Every other handler copies `currentTerm` unchanged. The "starts at `0`" part is **not encoded**: the constructor `init` accepts an arbitrary `currentTerm : ℕ`.
4. *"Versions are `Int` (Java `long`)."* Lean's `Int` is unbounded. Java's message constructors assert non-negative versions (Join.java:60-62, PublishResponse.java:52-53). Nothing in the Lean excludes negative versions.
5. *"A `ClusterState` is reduced to the fields that `CoordinationState` reads or writes; everything else is an opaque payload `value : V`."* See declaration 15.
6. *"`VotingConfiguration` stores its node ids strictly sorted, so that `=` is Java's `Set.equals`."* This holds (declarations 4–5).
7. *"The REMOTE persisted state ... is omitted. The handlers read it only to decide whether to write it (CS:616-642), and every value they compute is read from the LOCAL persisted state."*
   - In Java, `handlePublishRequest` (CS:454-456) and `handleCommit` (CS:569-571) consult the helpers at CS:617-642.
   - The third remote write inside a transcribed handler is `handlePreCommit()` (CS:593-599), called from `handlePublishResponse` at CS:510. It is governed by the settings flag `isRemoteStateEnabled` (CS:595), not by those helpers, and it feeds no computed value.
   - *"A failed remote write makes the Java method throw after its local effects (for example after `publishVotes.addVote` in `handlePublishResponse`, CS:503-510)"*: `addVote` is at CS:503 and `handlePreCommit()` at CS:510, so this is accurate.
   - *"the transcription returns the result instead, which only adds behaviours"*: in the Lean, each handler has a single deterministic outcome per input. No outcome represents "local effect done, then failure". Whether returning the result "only adds behaviours" depends on how a caller consumes results, which is not in this file. It cannot be checked here.
8. *"Java `assert`s ... are caller contracts. The handlers below do not check them; the cluster model states them as preconditions of the corresponding steps."* No cluster model is in this file. The file names two assertion groups as propositions, `initialStateContract` and `clientValueContract`, and no definition in the file uses either. Several other Java assertions have no Lean counterpart here:
   - `join.targetMatches(localNode)` (CS:265);
   - "won never becomes not won" (CS:323);
   - committed equals accepted after commit (CS:572);
   - the cluster-UUID/Zen1 assertion (CS:708-710);
   - non-negativity in the message constructors.

## 1. `NodeId`

`abbrev NodeId := Nat`: node ids are natural numbers.

## 2. `DiscoveryNode`

A structure with fields `id : NodeId` and `isClusterManagerNode : Bool`, deriving `DecidableEq` and `Repr`. Two nodes are equal iff both fields are equal.

**Java check.** Java's `DiscoveryNode` has more fields. Its `equals` compares *ephemeral ids* (DiscoveryNode.java:606-617), which this structure lacks. `isClusterManagerNode()` means "roles contain `MASTER_ROLE` or `CLUSTER_MANAGER_ROLE`" (DiscoveryNode.java:507-509); here it is a free Boolean.

No definition in the file compares two `DiscoveryNode`s. Nodes are inspected only through `id` and `isClusterManagerNode`.

## 3. `ZEN1_BWC_TERM`

`def ZEN1_BWC_TERM : Nat := 0`. This matches `public static final long ZEN1_BWC_TERM = 0;` at Coordinator.java:134.

## 4. `VotingConfiguration`

A structure with two fields:

- `nodeIds : List NodeId`;
- `sorted`, a proof that `nodeIds` is pairwise strictly increasing: every earlier entry is $<$ every later entry.

So the list has no duplicates, and every finite set of naturals has exactly one representation.

**Java check.** CM:383-449 wraps an unmodifiable `Set<String> nodeIds`. The constant `MUST_JOIN_ELECTED_CLUSTER_MANAGER` (CM:386-388) is not transcribed.

## 5. `instance : DecidableEq VotingConfiguration`

Two configurations are equal iff their `nodeIds` lists are equal; the proof field is irrelevant. With sortedness, this is equality of the represented sets.

**Java check.** `equals` compares the `nodeIds` sets (CM:420-426). Matches.

## 6. `VotingConfiguration.EMPTY_CONFIG`

The configuration with `nodeIds = []`. Matches CM:385. Equality is by `nodeIds`, so every configuration whose list is empty equals `EMPTY_CONFIG`.

## 7. `VotingConfiguration.isEmpty`

$\mathrm{isEmpty}(c) = \mathrm{true} \iff c.\mathrm{nodeIds} = [\,]$. Matches CM:433-435.

## 8. `VotingConfiguration.hasQuorum`

For a configuration $c$ and a list $L$ of ids:
$$\mathrm{hasQuorum}(c, L) = \mathrm{true} \iff 2\cdot\big|\,[\,x \in c.\mathrm{nodeIds} \mid x \in L\,]\,\big| \;>\; |c.\mathrm{nodeIds}|.$$
The bracket is the sublist of $c.\mathrm{nodeIds}$ whose entries occur in $L$; membership is tested with `List.contains` on ℕ. Let $N$ be the set of ids of $c$. Since $c.\mathrm{nodeIds}$ is duplicate-free, the condition is $2\,|N \cap L| > |N|$: a strict majority of $c$.

- Duplicates in $L$ do not matter.
- Entries of $L$ outside $N$ do not matter.
- For the empty configuration the test is $0 > 0$, which is false for every $L$.

**Java check.** CM:405-409 computes `intersection = copy of nodeIds; intersection.retainAll(votes); intersection.size() * 2 > nodeIds.size()`. Matches. Java uses `int` arithmetic; the Lean uses ℕ.

## 9. `VoteCollection`

A structure with one field, `nodes : List NodeId` (the docstring says "most recent first"). It derives `DecidableEq` and `Repr`, so two collections are equal iff their lists are equal: order and multiplicity matter.

**Java check.** CS:750-814 keeps a `Map<String, DiscoveryNode>` keyed by id plus a `Set<Join>`.

- The docstring says the joins are read only by tests. Confirmed: in the repository's main code, the only reader of `getJoins()` is `containsJoin` (CS:164-167, commented "used for tests").
- Java's `equals` (CS:798-806) compares the map and the join set without regard to order. The Lean equality is list equality.

The type does not forbid duplicate ids or ids of ineligible nodes. Such values cannot arise from `empty` and `addVote`, but they can appear in an arbitrary `CoordinationState`.

## 10. `VoteCollection.empty`

$\langle [\,]\rangle$. Matches Java `new VoteCollection()`.

## 11. `VoteCollection.addVote`

For a collection $v$ and a node $n$, it returns a pair (new collection, added?):

- if $n.\mathrm{isClusterManagerNode} = \mathrm{true}$ and $n.\mathrm{id} \notin v.\mathrm{nodes}$: $(\langle n.\mathrm{id} :: v.\mathrm{nodes}\rangle,\ \mathrm{true})$, with the id prepended;
- otherwise: $(v,\ \mathrm{false})$.

**Java check.** CS:755-757 is `sourceNode.isClusterManagerNode() && nodes.put(sourceNode.getId(), sourceNode) == null`. Matches:

- Because `&&` short-circuits, an ineligible node is not inserted.
- For an eligible node that is already present, Java's `put` replaces the stored `DiscoveryNode` object but leaves the key set unchanged and returns non-null. The ids-only model cannot see the replacement.

## 12. `VoteCollection.isQuorum`

$\mathrm{isQuorum}(v, c) = \mathrm{hasQuorum}(c, v.\mathrm{nodes})$. Matches CS:772-774.

## 13. `VoteCollection.containsVoteFor`

$\mathrm{containsVoteFor}(v, n) = \mathrm{true} \iff n.\mathrm{id} \in v.\mathrm{nodes}$. Matches CS:776-778. No other declaration in the file uses it.

## 14. `VoteCollection.isEmpty`

$\mathrm{isEmpty}(v) = \mathrm{true} \iff v.\mathrm{nodes} = [\,]$. Matches CS:780-782.

## 15. `ClusterState V`

For any type $V$, a structure with nine independent fields and no deriving clause:

| field | type | docstring / Java |
|---|---|---|
| `term` | ℕ | `term()`, i.e. `coordinationMetadata().term()` (CLS:227-229) |
| `version` | ℤ | `version()` |
| `metadataVersion` | ℤ | `metadata().version()` |
| `lastCommittedConfiguration` | `VotingConfiguration` | `getLastCommittedConfiguration()` |
| `lastAcceptedConfiguration` | `VotingConfiguration` | `getLastAcceptedConfiguration()` |
| `clusterManagerNode` | `Option ℕ` | `nodes().getClusterManagerNode()`, identified by its *ephemeral* id; `none` is Java `null` |
| `clusterUUIDKnown` | `Bool` | cluster UUID ≠ `UNKNOWN_CLUSTER_UUID` |
| `clusterUUIDCommitted` | `Bool` | `metadata().clusterUUIDCommitted()` |
| `value` | $V$ | "everything else" |

Three points about these fields:

- **No constraints among fields.** Nothing forces `clusterUUIDCommitted → clusterUUIDKnown`, non-negative versions, or any relation between `version` and `metadataVersion`.
- **`clusterManagerNode` uses its own numbering.** It is a natural number in a separate identifier space from `NodeId`, and nothing links the two.
- **Its docstring checks out.** It says the field is read only by the Zen1 branch of `handlePublishRequest`; that is accurate within this file. Java's `DiscoveryNode.equals` does compare ephemeral ids, and `DiscoveryNodes.getClusterManagerNode()` returns `null` when no cluster manager is set (DiscoveryNodes.java:287-292).

## 16. `ClusterState.versionOrMetadataVersion`

$$\mathrm{versionOrMetadataVersion}(s) = \begin{cases} s.\mathrm{metadataVersion} & \text{if } s.\mathrm{term} = \mathrm{ZEN1\_BWC\_TERM} = 0,\\ s.\mathrm{version} & \text{otherwise.}\end{cases}$$
Matches CLS:239-244 (`term() == ZEN1_BWC_TERM ? metadata().version() : version()`).

## 17. `ClusterState.markCommitted`

The function runs in two steps:

1. Let $s_1$ be "$s$ with `lastCommittedConfiguration` $:= s.\mathrm{lastAcceptedConfiguration}$" if the two configurations of $s$ differ, and $s$ otherwise.
2. If $s_1.\mathrm{clusterUUIDKnown} = \mathrm{true}$ and $s_1.\mathrm{clusterUUIDCommitted} = \mathrm{false}$, return $s_1$ with `clusterUUIDCommitted` $:= \mathrm{true}$. Otherwise return $s_1$.

In both branches of step 1, $s_1$ ends with committed configuration equal to $s$'s accepted configuration. The net effect is:

- `lastCommittedConfiguration` becomes `lastAcceptedConfiguration`;
- `clusterUUIDCommitted` becomes `clusterUUIDCommitted || clusterUUIDKnown`;
- `term`, `version`, `metadataVersion`, `lastAcceptedConfiguration`, `clusterManagerNode`, `clusterUUIDKnown` and `value` are unchanged.

**Java check.** CS:703-728 with CS:730-740 matches:

- `commitVotingConfiguration` builds new metadata with the committed configuration replaced only if the two configurations differ.
- The UUID test runs on the original state; it reads the same flags as $s_1$.
- The state is rewritten only if something changed.
- The Java rebuild preserves the version and the metadata version: `ClusterState.Builder(ClusterState)` copies `version` (ClusterState.java:618-629), and `Metadata.Builder(Metadata)` copies `version` (Metadata.java:1231-1243).
- The assertion at CS:708-710 (cluster UUID known, or term = Zen1 term) is not modelled.
- In `server/src/main/java` the default method is overridden only by the *remote* `RemotePersistedState` (GatewayMetaState.java:830). The LOCAL persisted states inherit the default, so the default is what is transcribed.

## 18–22. Message structures

All five structures except `PublishRequest` derive `DecidableEq` and `Repr`:

- **`StartJoinRequest`**: `sourceNode : DiscoveryNode`, `term : ℕ`. Matches StartJoinRequest.java:53.
- **`Join`**: `sourceNode`, `targetNode : DiscoveryNode`, `term : ℕ`, `lastAcceptedTerm : ℕ`, `lastAcceptedVersion : ℤ`, in Java's constructor order (Join.java:59). Java asserts all three numbers are ≥ 0 (Join.java:60-62); the Lean allows a negative `lastAcceptedVersion`.
- **`PublishRequest V`**: `acceptedState : ClusterState V`, with no deriving clause. Matches PublishRequest.java:48.
- **`PublishResponse`**: `term : ℕ`, `version : ℤ`. Matches PublishResponse.java:51, which asserts both are ≥ 0.
- **`ApplyCommitRequest`**: `sourceNode : DiscoveryNode`, `term : ℕ`, `version : ℤ`. Matches ApplyCommitRequest.java:49.

## 23. `ElectionStrategy`

A structure with one field, `satisfiesAdditionalQuorumConstraints : DiscoveryNode → ℕ → ℕ → ℤ → VotingConfiguration → VotingConfiguration → VoteCollection → Bool`. It is an arbitrary total Boolean function, written $f_{es}$ below. Its arguments are, in order: local node, current term, accepted term, accepted version, committed configuration, accepted configuration, votes.

**Java check.** The argument order matches ES:101-109.

- *"`isElectionQuorum` is final"* matches ES:68.
- *"`DEFAULT_INSTANCE`, the only strategy in OpenSearch itself"*: a repository-wide search finds no other subclass or anonymous instance of `ElectionStrategy`.
- A Java strategy sees `DiscoveryNode` objects and the recorded joins. Here it sees only the vote ids, as the docstring says.

The `CoordinationState` structure has no strategy field (see 26). The strategy is an explicit argument to `isElectionQuorum`, `handleJoin` and `javaInvariant`. So nothing in the Lean ties one state to one strategy across calls, whereas Java stores it as a `final` field.

## 24. `ElectionStrategy.DEFAULT_INSTANCE`

$f(\dots) = \mathrm{true}$ for all arguments. Matches ES:46-59.

## 25. `ElectionStrategy.Monotone`

$\mathrm{Monotone}(es)$ is the proposition
$$\forall n\ t\ t'\ a\ c\ c'\ v\ w,\quad (\forall x,\ x \in v.\mathrm{nodes} \to x \in w.\mathrm{nodes}) \to f_{es}(n,t,t',a,c,c',v) = \mathrm{true} \to f_{es}(n,t,t',a,c,c',w) = \mathrm{true}.$$
Every argument other than the votes is held fixed, and inclusion is by membership. This is a Lean-only notion with no Java counterpart. The docstring's *"The default strategy is"* is the separate theorem `default_monotone`.

## 26. `CoordinationState V`

A structure with nine fields and no deriving clause:

- `localNode : DiscoveryNode`;
- `currentTerm : ℕ` (persisted, `getCurrentTerm()`);
- `lastAcceptedState : ClusterState V` (persisted, `getLastAcceptedState()`);
- `joinVotes : VoteCollection`;
- `startedJoinSinceLastReboot : Bool`;
- `electionWon : Bool`;
- `lastPublishedVersion : ℤ`;
- `lastPublishedConfiguration : VotingConfiguration`;
- `publishVotes : VoteCollection`.

**Java check.** CS:64-106 has these, plus three things not represented: the `electionStrategy` field, the `persistedStateRegistry` (whose LOCAL state's two components become `currentTerm` and `lastAcceptedState`), and `isRemoteStateEnabled`. No field constraints are imposed.

## 27. `CoordinationState.init`

`init(n, t, S)` takes any node $n$, any $t \in ℕ$ and any cluster state $S$, and returns the state:

- `localNode` $= n$;
- `currentTerm` $= t$;
- `lastAcceptedState` $= S$;
- `joinVotes` = `empty`;
- `startedJoinSinceLastReboot` = false;
- `electionWon` = false;
- `lastPublishedVersion` $= 0$;
- `lastPublishedConfiguration` $= S.\mathrm{lastAcceptedConfiguration}$;
- `publishVotes` = `empty`.

No relation between $t$ and $S.\mathrm{term}$ is required. Matches CS:84-106, including the defaults at lines 97-104.

## 28. Accessors (no docstrings)

Each reads a field of the last accepted state:

- $\mathrm{lat}(cs) := cs.\mathrm{lastAcceptedState}.\mathrm{term}$ (`lastAcceptedTerm`);
- $\mathrm{lav}(cs) := cs.\mathrm{lastAcceptedState}.\mathrm{version}$ (`lastAcceptedVersion`);
- $\mathrm{lavm}(cs) := \mathrm{versionOrMetadataVersion}(cs.\mathrm{lastAcceptedState})$ (`lastAcceptedVersionOrMetadataVersion`);
- $\mathrm{C}(cs) := cs.\mathrm{lastAcceptedState}.\mathrm{lastCommittedConfiguration}$;
- $\mathrm{A}(cs) := cs.\mathrm{lastAcceptedState}.\mathrm{lastAcceptedConfiguration}$.

These match CS:116-134.

## 29. `CoordinationState.isElectionQuorum`

$$\mathrm{isElectionQuorum}(es, cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{A}(cs)) \wedge f_{es}\big(cs.\mathrm{localNode}, cs.\mathrm{currentTerm}, \mathrm{lat}(cs), \mathrm{lav}(cs), \mathrm{C}(cs), \mathrm{A}(cs), v\big).$$
The function never reads `cs.joinVotes`; the votes are the argument $v$. The strategy receives the plain version $\mathrm{lav}$, not $\mathrm{lavm}$. Matches CS:144-154 and ES:68-88.

## 30. `CoordinationState.isPublishQuorum`

$\mathrm{isPublishQuorum}(cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, cs.\mathrm{lastPublishedConfiguration})$. Matches CS:156-158.

## 31. `CoordinationState.setInitialState`

`setInitialState(cs, S) : Except String (CoordinationState V)`:

1. If $\mathrm{A}(cs)$ is non-empty: $\mathrm{error}$ ("initial state already set…").
2. Otherwise: $\mathrm{ok}(cs \text{ with } \mathrm{lastAcceptedState} := S)$.

Nothing about $S$ is checked: not its term, version or configurations. `lastPublishedConfiguration` is not updated.

**Java check.** CS:180-204 matches. Java's assertions are not checked; they appear as `initialStateContract`.

## 32. `CoordinationState.initialStateContract`

A proposition about $(cs, S)$: the conjunction, in Java's order (CS:190-201), of

1. $\mathrm{lat}(cs) = 0$;
2. $\mathrm{isEmpty}(\mathrm{C}(cs))$;
3. $cs.\mathrm{lastPublishedVersion} = 0$;
4. $\mathrm{isEmpty}(cs.\mathrm{lastPublishedConfiguration})$;
5. $cs.\mathrm{electionWon} = \mathrm{false}$;
6. $\mathrm{isEmpty}(cs.\mathrm{joinVotes})$;
7. $\mathrm{isEmpty}(cs.\mathrm{publishVotes})$;
8. $S.\mathrm{term} = 0$;
9. $S.\mathrm{version} = \mathrm{lav}(cs)$;
10. $\mathrm{isEmpty}(S.\mathrm{lastAcceptedConfiguration}) = \mathrm{false}$;
11. $\mathrm{isEmpty}(S.\mathrm{lastCommittedConfiguration}) = \mathrm{false}$.

All 11 Java assertions are present. No other declaration in this file uses it, and none of the mission's theorem statements does.

## 33. `CoordinationState.handleStartJoin`

`handleStartJoin(cs, r) : Except String (CoordinationState V × Join)`:

1. If $r.\mathrm{term} \le cs.\mathrm{currentTerm}$: $\mathrm{error}$.
2. Otherwise: $\mathrm{ok}(cs', J)$, where:
   - $cs'$ is $cs$ with `currentTerm` $:= r.\mathrm{term}$, `lastPublishedVersion` $:= 0$, `lastPublishedConfiguration` $:= \mathrm{A}(cs)$, `startedJoinSinceLastReboot` $:=$ true, `electionWon` $:=$ false, `joinVotes` $:=$ `empty`, `publishVotes` $:=$ `empty`. `localNode` and `lastAcceptedState` are unchanged.
   - $J = \mathrm{Join}(\text{source} = cs.\mathrm{localNode},\ \text{target} = r.\mathrm{sourceNode},\ \text{term} = r.\mathrm{term},\ \text{lastAcceptedTerm} = \mathrm{lat}(cs),\ \text{lastAcceptedVersion} = \mathrm{lavm}(cs))$.

Nothing about $r.\mathrm{sourceNode}$ is checked.

**Java check.** CS:213-255 matches: same guard, same assignments, the same `Join` (Java's `getCurrentTerm()` at line 251 is the new term), and `setCurrentTerm` does not affect the accepted state (CS:661-666). The log-only branch at CS:227-237 has no effect.

## 34. `CoordinationState.handleJoin`

`handleJoin(es, cs, j) : Except String (CoordinationState V × Bool)`. The guards are tested in this order, and the first that fires gives $\mathrm{error}$:

1. $j.\mathrm{term} \ne cs.\mathrm{currentTerm}$;
2. $cs.\mathrm{startedJoinSinceLastReboot} = \mathrm{false}$;
3. $j.\mathrm{lastAcceptedTerm} > \mathrm{lat}(cs)$;
4. $j.\mathrm{lastAcceptedTerm} = \mathrm{lat}(cs)$ and $j.\mathrm{lastAcceptedVersion} > \mathrm{lavm}(cs)$, compared against the *version-or-metadata-version*;
5. $\mathrm{isEmpty}(\mathrm{A}(cs))$.

Otherwise the handler computes:

- $(v', \mathit{added}) := \mathrm{addVote}(cs.\mathrm{joinVotes}, j.\mathrm{sourceNode})$;
- $\mathit{won} := \mathrm{isElectionQuorum}(es, cs, v')$, evaluated on the old state $cs$, whose relevant fields are unchanged;
- $cs_1 := cs$ with `joinVotes` $:= v'$, `electionWon` $:= \mathit{won}$;
- $cs_2 := cs_1$ with `lastPublishedVersion` $:= \mathrm{lav}(cs)$ if $\mathit{won} = \mathrm{true}$ and $cs.\mathrm{electionWon} = \mathrm{false}$; otherwise $cs_2 := cs_1$.

The result is $\mathrm{ok}(cs_2, \mathit{added})$.

Two points:

- `electionWon` is **recomputed**, not only raised. In a state whose flag disagrees with the quorum test, a join can lower it.
- $j.\mathrm{targetNode}$ is never read. Java asserts it is the local node (CS:265).

**Java check.** CS:264-339 matches: guard order, `addJoinVote` reducing to `addVote` on the source node (CS:759-765), the election test using `getLastAcceptedVersion()` (CS:149), and `lastPublishedVersion = getLastAcceptedVersion()` on a fresh win (CS:334-337). The assertion at CS:323 is not checked.

## 35. `CoordinationState.handleClientValue`

`handleClientValue(cs, S) : Except String (CoordinationState V × PublishRequest V)`. The guards are tested in this order, and the first that fires gives $\mathrm{error}$:

1. $cs.\mathrm{electionWon} = \mathrm{false}$;
2. $cs.\mathrm{lastPublishedVersion} \ne \mathrm{lav}(cs)$;
3. $S.\mathrm{term} \ne cs.\mathrm{currentTerm}$;
4. $S.\mathrm{version} \le cs.\mathrm{lastPublishedVersion}$;
5. $S.\mathrm{lastAcceptedConfiguration} \ne \mathrm{A}(cs)$ and $\mathrm{C}(cs) \ne \mathrm{A}(cs)$;
6. $\mathrm{isQuorum}(cs.\mathrm{joinVotes}, S.\mathrm{lastAcceptedConfiguration}) = \mathrm{false}$.

Otherwise the result is $\mathrm{ok}(cs \text{ with } \mathrm{lastPublishedVersion} := S.\mathrm{version},\ \mathrm{lastPublishedConfiguration} := S.\mathrm{lastAcceptedConfiguration},\ \mathrm{publishVotes} := \mathrm{empty};\ \mathrm{PublishRequest}(S))$.

$S.\mathrm{lastCommittedConfiguration}$ is not checked; the Java assertion appears as `clientValueContract`. Nor are $S$'s other fields.

**Java check.** CS:348-407 matches.

## 36. `CoordinationState.clientValueContract`

$\mathrm{clientValueContract}(cs, S) :\iff S.\mathrm{lastCommittedConfiguration} = \mathrm{C}(cs)$. Matches CS:397-398. No other declaration in this file uses it, and none of the mission's theorem statements does.

## 37. `CoordinationState.handlePublishRequest`

`handlePublishRequest(cs, R) : Except String (CoordinationState V × PublishResponse)`. Let $S = R.\mathrm{acceptedState}$. Define $\mathit{accept} := \mathrm{ok}(cs \text{ with } \mathrm{lastAcceptedState} := S,\ \mathrm{PublishResponse}(S.\mathrm{term}, S.\mathrm{version}))$. Then:

1. If $S.\mathrm{term} \ne cs.\mathrm{currentTerm}$: $\mathrm{error}$.
2. Else if $S.\mathrm{term} = \mathrm{lat}(cs)$ and $S.\mathrm{version} \le \mathrm{lav}(cs)$ (a stale or equal version in the accepted term):
   - if $S.\mathrm{term} = 0$ (the Zen1 branch, so $cs.\mathrm{currentTerm} = \mathrm{lat}(cs) = 0$ here):
     - if $S.\mathrm{clusterManagerNode} = \mathrm{none}$: $\mathrm{error}$("NullPointerException");
     - if $S.\mathrm{clusterManagerNode} = \mathrm{some}\ m$: $\mathit{accept}$ when $\mathrm{some}\ m \ne cs.\mathrm{lastAcceptedState}.\mathrm{clusterManagerNode}$ (the stored value is `none` or a different number), and $\mathrm{error}$ otherwise;
   - otherwise: $\mathrm{error}$.
3. Else: $\mathit{accept}$.

The handler touches only `lastAcceptedState`. Every field of $S$ (configurations included) is adopted unchecked, and `electionWon` is left as is.

**Java check.** CS:416-460 matches.

- When the incoming cluster manager is `null`, Java's `getClusterManagerNode().equals(...)` throws a `NullPointerException` (not a `CoordinationStateRejectedException`). The Lean merges this into $\mathrm{error}$.
- `x.equals(null)` is false, which matches accepting when the stored value is `none`.

## 38. `CoordinationState.handlePublishResponse`

`handlePublishResponse(cs, n, r) : Except String (CoordinationState V × Option ApplyCommitRequest)`. The guards are tested in this order, and the first that fires gives $\mathrm{error}$:

1. $cs.\mathrm{electionWon} = \mathrm{false}$;
2. $r.\mathrm{term} \ne cs.\mathrm{currentTerm}$;
3. $r.\mathrm{version} \ne cs.\mathrm{lastPublishedVersion}$.

Otherwise the handler computes:

- $v' := \mathrm{addVote}(cs.\mathrm{publishVotes}, n).1$; the "added" Boolean is discarded;
- $cs' := cs$ with `publishVotes` $:= v'$;
- the result is $\mathrm{ok}(cs', \mathrm{some}\ \mathrm{ApplyCommitRequest}(cs.\mathrm{localNode}, r.\mathrm{term}, r.\mathrm{version}))$ if $\mathrm{isPublishQuorum}(cs', v')$, that is, $v'$ is a quorum of $\mathrm{C}(cs)$ and of $cs.\mathrm{lastPublishedConfiguration}$. Otherwise the result is $\mathrm{ok}(cs', \mathrm{none})$.

A commit request is returned on *every* successful call once the votes form a publish quorum, including repeated responses from the same node.

**Java check.** CS:471-515 matches. The remote `handlePreCommit()` (CS:510) is omitted, as discussed above.

## 39. `CoordinationState.handleCommit`

`handleCommit(cs, c) : Except String (CoordinationState V)`. The guards are tested in this order:

1. $c.\mathrm{term} \ne cs.\mathrm{currentTerm}$: $\mathrm{error}$;
2. $c.\mathrm{term} \ne \mathrm{lat}(cs)$: $\mathrm{error}$;
3. $c.\mathrm{version} \ne \mathrm{lav}(cs)$: $\mathrm{error}$.

Otherwise the result is $\mathrm{ok}(cs \text{ with } \mathrm{lastAcceptedState} := \mathrm{markCommitted}(cs.\mathrm{lastAcceptedState}))$. $c.\mathrm{sourceNode}$ is never read.

**Java check.** CS:523-573 matches: the LOCAL `markLastAcceptedStateAsCommitted`, the default method (see 17). The REMOTE commit is omitted.

## 40. `CoordinationState.javaInvariant`

$\mathrm{javaInvariant}(es, cs)$ is the conjunction of:

- (i) $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$;
- (ii) $cs.\mathrm{electionWon} = \mathrm{isElectionQuorum}(es, cs, cs.\mathrm{joinVotes})$, an equality of Booleans;
- (iii) if $cs.\mathrm{electionWon}$ then $cs.\mathrm{lastPublishedVersion} \ge \mathrm{lav}(cs)$, else $cs.\mathrm{lastPublishedVersion} = 0$;
- (iv) $cs.\mathrm{electionWon} = \mathrm{true} \to cs.\mathrm{startedJoinSinceLastReboot} = \mathrm{true}$;
- (v) $\mathrm{isEmpty}(cs.\mathrm{publishVotes}) = \mathrm{true} \lor cs.\mathrm{electionWon} = \mathrm{true}$.

Matches `invariant()` at CS:601-611, assertion by assertion.

## Summary of transcription fidelity

Every handler, quorum test and helper reproduces the cited Java (local persisted state only):

- the order of guards;
- the comparisons, including the asymmetric use of $\mathrm{lavm}$ in `handleJoin`'s guard versus $\mathrm{lav}$ in the strategy call and in the new published version;
- the assignments;
- the returned messages.

The deliberate deviations are all stated in the docstrings:

- the remote store and its write failures are omitted;
- assertions are not checked;
- a `null` incoming cluster manager becomes an error;
- vote collections hold ids only;
- a strategy sees ids only.

Things the docstrings do not spell out:

- the strategy is passed per call rather than fixed per state;
- `init` does not force the initial term to be 0;
- `VoteCollection` equality is order- and multiplicity-sensitive;
- message-constructor non-negativity is not modelled.
