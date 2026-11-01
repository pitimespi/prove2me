# OpenSearch cluster coordination: safety of the cluster (`OpenSearchSafety`)

Mission over OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, built on the per-node transcription of
`CoordinationState` (mission `OpenSearchCoordination`, see `NOTES_OpenSearchCoordination.md`). 44 theorems, all proved.

- Model, safety vocabulary and invariant: `Definitions/Def_OpenSearchSafety.lean` (imports
  `Def_OpenSearchCoordination`, nothing else).
- Proofs: `Solutions/Sol_OpenSearchSafety_static_all.lean` (22 theorems: consequences of the invariant inside one
  cluster), `Solutions/Sol_OpenSearchSafety_steps_all.lean` (10: the invariant holds initially and is preserved by each
  kind of step), `Solutions/Sol_OpenSearchSafety_all.lean` (12: `reachable_inv`, the ten public safety statements,
  `commit_reachable`); the 44 split files `Solutions/Sol_OpenSearchSafety_<name>.lean` and the statement stubs
  `Theorems/Thm_OpenSearchSafety_<name>.lean`.
- Prose: `missions/items/ossafety_items.py`, `missions/descriptions/ossafety_description.md`,
  `missions/explanations/expl_OpenSearchSafety_*.md` (one per theorem).
- Goal theorem: `OpenSearchSafety.committed_linear` (committed states never fork), which is the "main invariant" of
  Elastic's TLA+ model, `CommittedValuesDescendantsFromCommittedValues`; the items leave no milestone on it.
  `leader_completeness` (every publication of a later term descends from every committed one) is the lemma behind it;
  it says more about publications of later terms but nothing about two commits of the same term.

Citations in the Lean file: `CO` Coordinator.java and `CBS` ClusterBootstrapService.java (both in
`server/src/main/java/org/opensearch/cluster/coordination/`), `GatewayMetaState.java`
(`server/src/main/java/org/opensearch/gateway/`), with line numbers at the pinned revision; `CS` is
CoordinationState.java, as in the per-node mission. "TLA+" is Elastic's `ZenWithTerms.tla`
(`elastic/elasticsearch-formal-models` at `ca30663`), the formal model cited at CS:60. "Design 1" and "design 2" are
the two paper invariants validated by model checking before the Lean proof (section "Validation by model checking");
the labels P1, C1, N3, L4, ... in the docstrings of `Inv` are design 1's names for its conjuncts.

## The model

### Parameters and clusters

`Params` fixes, for the whole execution: `eligible n`, whether node `n` has the cluster-manager role (fixed: see
"Assumptions"); `initConfs`, the configurations a node may bootstrap with (a predicate, so possibly several); and
`strategy`, the election strategy used by every node. `P.dn n = ⟨n, P.eligible n⟩` is node `n`'s `DiscoveryNode`.

A `Cluster V` is `node : NodeId → CoordinationState V`, the state of every node id (nodes that never take a step are
simply idle), and `sent : Message V → Prop`, the messages sent so far. `W.set n cs` replaces a node's state,
`W.send m` adds a message.

### Messages and the network

`Message V` has four kinds: `join j`; `publishRequest source state parentTerm parentVersion`; `publishResponse source
dest resp`; `applyCommit c`. A message, once sent, stays in `sent` forever, and a step may handle any sent message
any number of times, in any order, or never: this is loss, duplication, delay and reordering at once. A join is
handled only by its target and a publish response only by its addressee; a publish request or a commit may be handled
by any node (Java sends a publication to the nodes of the published state and the commit to those that accepted it,
Publication.java:80-84, 290-304; the model allows more).

Start-join requests are not messages. A `startJoin` step lets any node handle, at any time, a request from any
cluster-manager-eligible node for any term. Every start-join request the `Coordinator` builds has an eligible
requester: the candidate itself in `startElection` (CO:593; the election scheduler runs only on eligible nodes,
CO:1567-1571), the node abdicated to (asserted eligible, CO:604-609), and the requester that each caller passes to
`ensureTermAtLeast` (CO:635-641): the cluster-manager sending a follower check of a higher term (CO:391), the
publisher of a state of a higher term (`handlePublishRequest`, CO:512), the node itself as leader after seeing a higher
term (CO:572), the node itself when it receives a join of a higher term (CO:1269; only eligible nodes receive joins,
CO:661), and a discovered active cluster-manager (CO:1521).

### Steps

`Step P W W'` has nine constructors. Each is a successful call at a node `n`; `W'` replaces `n`'s state by the
handler's result and adds the handler's output, if any.

| step | call at node `n` | further hypotheses | added to `sent` |
|---|---|---|---|
| `bootstrap` | `setInitialState s` | `P.initConfs X`, both configurations of `s` equal `X`, `initialStateContract` (the asserted preconditions, CS:190-201) | nothing |
| `startJoin` | `handleStartJoin ⟨P.dn src, t⟩` | `P.eligible src` | the `Join` (to `src`) |
| `join` | `handleJoin P.strategy j` | `j` sent, `j.targetNode.id = n` | nothing |
| `clientValue` | `handleClientValue s` | `clientValueContract` (`s` carries `n`'s last committed configuration, CS:397-398) | `publishRequest n s lt lv`, with `(lt, lv)` = `n`'s last accepted term and version before the call |
| `publish` | `handlePublishRequest ⟨s⟩` | `publishRequest src s pt pv` sent | `publishResponse n src r` |
| `respond` | `handlePublishResponse (P.dn src) r` | `publishResponse src n r` sent | `applyCommit c` if a commit `c` is returned |
| `commit` | `handleCommit c` | `applyCommit c` sent | nothing |
| `restart` | state := `init localNode currentTerm s'` | `P.eligible n`, `RestartState lastAcceptedState s'` | nothing |
| `restartAny` | state := `init localNode t s'` (any `t`, `s'`) | `P.eligible n = false` | nothing |

The steps cover every call the `Coordinator` makes into `CoordinationState`: `setInitialConfiguration`
(CO:1101-1161, called by `ClusterBootstrapService`), `joinLeaderInTerm` (CO:643-657), `handleJoin` (CO:1267-1299),
`publish` (handleClientValue at CO:1404), `handlePublishRequest` (CO:454-526), the publication's
`handlePublishResponse` (CO:1871-1876), `handleApplyCommit` (CO:419-452). The `Coordinator`'s own conditions (its
mode, the single publication in progress, join validation, the cluster-UUID check of CO:488-505, timeouts) only make
it call less, so every sequence of its calls is a path of `Step`. This is an argument from the code: the `Coordinator`
itself is not transcribed. The model over-approximates it: start-joins of arbitrary terms, any elected node publishing
any state its guards allow, redelivery of every message.

Java `assert`s are off in production. The asserted preconditions of `setInitialState` and `handleClientValue` are
imposed at the `bootstrap` and `clientValue` steps: they are obligations of the callers, which Java states only as
assertions (for bootstrapping, `setInitialConfiguration` builds the initial state from the current, unbootstrapped one,
CO:1144-1154). The asserted `join.targetMatches(localNode)` (CS:265) holds because a join is handled only by its
target.

### Restarts

A cluster-manager-eligible node persists its current term and accepted state synchronously (`LucenePersistedState`,
GatewayMetaState.java:199-200). On startup it rebuilds the parts of the accepted state that are not persisted: the
cluster state is rebuilt from the persisted version and metadata (GatewayMetaState.java:164-167, 190-197), so its node
list, routing table and transient settings are new. `RestartState s s'` therefore keeps the term, the version, both
configurations and both cluster-UUID flags; it also lets the metadata version, the cluster-manager node and the payload
change, which over-approximates Java (the metadata, metadata version included, is persisted and reloaded) and only adds
behaviours. With the remote cluster-state store enabled, an eligible node whose persisted cluster UUID is unknown, and
for which the store knows a cluster UUID, restores index metadata and settings from the store into an empty metadata
(GatewayMetaState.java:169-188, 287-300), so its state then has term 0 and empty configurations. The model's trigger is
narrower: a node may come back with any term-0 state with empty configurations only if its state has term 0, empty
configurations and an unknown UUID. No Java behaviour is lost: Java generates the cluster UUID when it bootstraps
(`setInitialConfiguration`, CO:1151), and a state of term ≥ 1 is published by an elected node and carries its cluster
UUID (CS:708-710 asserts a known UUID when such a state is committed), so a Java node with an unknown UUID has term 0
and empty configurations. The model's `bootstrap` and `clientValue` steps leave the UUID flags free, so a model state of
term ≥ 1 or with non-empty configurations may have an unknown UUID; such a state has no remote restore in the model,
and Java has no such state. The current term is kept. The transient state is the constructor's: no votes, no started
join, no election won, last published version 0.

A node that is not cluster-manager-eligible persists asynchronously (`AsyncLucenePersistedState`,
GatewayMetaState.java:201-206), or, without the data role, not at all (GatewayMetaState.java:232-255), so
`restartAny` lets it come back with any term and any accepted state.

### Bootstrap configurations

A node bootstraps (`ClusterBootstrapService.onFoundPeersUpdated`, CBS:176-215) once it has matched more than half of
the requirements listed in `cluster.initial_cluster_manager_nodes` (CBS:211) with discovered nodes; its configuration
contains the matched nodes and a placeholder `"{bootstrap-placeholder}-" + requirement` for each unmatched requirement
(`startBootstrap`, CBS:259-273; `checkRequirements`, CBS:306-335). Nodes that have discovered different subsets
bootstrap with different configurations, so `initConfs` is a set of configurations, and the theorems assume
`P.InitCompatible`: for any two bootstrap configurations, a list of eligible nodes forming a quorum of one and a list
of eligible nodes forming a quorum of the other share a node. `BootstrapConfig k resolve placeholder matched X`
describes the form of `ClusterBootstrapService`'s configurations, and `bootstrap_compatible` proves them compatible,
provided `resolve` is injective on the requirements (each requirement names its own node, the same at every node),
placeholders are pairwise distinct and distinct from resolved ids, and placeholders are not eligible node ids. The
theorem is stated for a standalone eligibility function and does not mention `Params`, and no definition of the model
refers to `BootstrapConfig` (the `bootstrap` step uses `P.initConfs`): that `P.initConfs` consists of such
configurations is part of the modelling, and the safety theorems keep `P.InitCompatible` as a hypothesis. The
"best-effort" bootstrap that runs only when no discovery setting is configured (CBS:217-250) uses whatever nodes were
discovered and is not covered.

### Ghost parents, descent and commits

Each `publishRequest` records the publisher's last accepted term and version when it published, its *parent*. The
real message does not carry it and no handler reads it; it defines the history in which the theorems are stated. A
publication is named by its *key* (term, version).

- `Committed W t v`: an `applyCommit ⟨src, t, v⟩` has been sent.
- `Parent W t v t' v'`: a publication of key `(t', v')` was sent with parent `(t, v)`.
- `Descends W t v t' v'`: the reflexive-transitive closure of `Parent`.

### Initial clusters

`Initial P W`: every node `n` is `CoordinationState.init (P.dn n) 0 s` for a term-0 state `s` with empty
configurations, and nothing has been sent. The version, metadata version, cluster-manager node, cluster-UUID flags and
payload of `s` are arbitrary and may differ between nodes: a fresh node has version 0, but a node upgraded from an older
version or restored from the remote store may have others.

## The safety statements

Hypotheses common to all but `bootstrap_compatible` and `commit_reachable`: `P.InitCompatible` and
`P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and `Reachable P W` (`W` is reached from an initial cluster by steps).

| theorem | statement | TLA+ counterpart |
|---|---|---|
| `reachable_inv` | `Inv P W` | — |
| `one_master_per_term` | two publications of the same term have the same source | `OneMasterPerTerm` |
| `one_state_per_version` | two publications with the same key are the same message: source, cluster state (every field, payload included) and parent | `LogMatching` (values only) |
| `leader_completeness` | a committed key is an ancestor-or-self of the key of every publication of a later term | `NewerOpsBasedOnOlderCommittedOps` (later terms) |
| `committed_linear` (goal) | two committed keys are related by descent | `CommittedValuesDescendantsFromCommittedValues` ("main invariant") |
| `committed_versions` | equal committed versions have equal terms; committed versions increase with the term | `P2bInvariant` (for committed publications) |
| `committed_published` | every commit is of a publication | — |
| `election_safety` | two nodes that hold a won election at the same moment, in the same current term, are the same node | — |
| `javaInvariant_reachable` | at every eligible node, the five assertions of `CoordinationState.invariant()` (CS:601-611) | `SingleNodeInvariant` |
| `lastCommitted_committed` | an eligible node's last committed configuration is empty, a bootstrap configuration, or the last accepted configuration of a committed publication | — |
| `bootstrap_compatible` | two configurations of `ClusterBootstrapService`'s form (`BootstrapConfig`, same requirements and resolution) meet the condition of `InitCompatible` (own hypotheses, above; `Params` is not mentioned) | — |
| `commit_reachable` | some `P`, `W` satisfy `InitCompatible`, the default strategy, `Reachable` and `Committed W 1 1` | — |

`NewerOpsBasedOnOlderCommittedOps` also covers publications of the committed key's own term with a larger version;
that case follows from `inv_committed_published`, `pub_same_term` and `inv_descends_key`. `P2bInvariant` (a publication of a later term than a
commit has a larger version) follows from `leader_completeness` and `inv_descends_key`. TLA+'s
`DescendantRelationIsStrictlyOrdered` is `pub_wf` (and `inv_descends_key`).

`javaInvariant_reachable` is restricted to eligible nodes because a node that is not eligible may restart with an
accepted term above its current term. Not every handler preserves `invariant()` on its own: `handlePublishRequest` can
break it (`OpenSearchCoordination.javaInvariant_not_local`); it holds because of what the rest of the cluster did.

## The invariant

### Proof-side notions

Defined after the model in `Def_OpenSearchSafety.lean`; the model does not use them. They are relations, never
functions computed from the sent messages: `KeyLE` and `Below` compare keys, `Won` also reads node states (it becomes
false when a node that has not published loses its election), and the others depend on the sent messages only, so they
only grow when messages are sent. Every list of voters consists of eligible nodes, so that `InitCompatible` applies to
it.

- `KeyLE t v t' v'`: the lexicographic order on keys.
- `Below lt lv bt bv`: `lt < bt ∨ (lt = bt ∧ (bt = 0 ∨ lv ≤ bv))`. This is `handleJoin`'s freshness test with
  the version ignored at term 0: a term-0 state's join carries its metadata version (`versionOrMetadataVersion`),
  which plays no role in safety.
- `Published W t v`: a publication of key `(t, v)` was sent.
- `Realizes P W t v x y`: the pair (last committed, last accepted) `(x, y)` is one a node can hold at key `(t, v)`:
  `t = 0` and `x = y` is a bootstrap configuration; or a sent publication of key `(t, v)` has last accepted
  configuration `y` and last committed configuration `x`, or has last accepted configuration `x` and is committed (a
  node that applied the commit, `markCommitted`).
- `JoinVoters P W L t J`: every member of `J` is eligible and sent `L` a join of term `t`.
- `BaseVoters P W L t bt bv J`: the same, with each join's last accepted (term, version) `Below (bt, bv)`.
- `RespVoters P W t v A`: every member of `A` is eligible and sent a `PublishResponse ⟨t, v⟩` (to some node).
- `ElectionRecord P W L t bt bv x y J`: `bt < t`, `(x, y)` realizes the base `(bt, bv)`, `BaseVoters P W L t bt bv J`,
  and `J` is a quorum of `x` and of `y`. A node that has just won the election of term `t` from accepted key
  `(bt, bv)` has one, and so does the first publication of a term (its publisher's state when it won). Design 2 calls
  this an "election situation".
- `Won P W b t`: `b` is eligible and either has `electionWon` in current term `t`, or has sent a publication of term
  `t`.

### The fields

`Inv P W` has 30 fields, grouped as in design 1. Facts about persisted state are stated for eligible nodes only,
because a node that is not eligible may restart with any persisted state; facts about transient state hold for every
node, because a node that is not eligible is never the target of a join, so never holds votes or wins. Notation for a
node: current term `ct`, last accepted term/version `lat`/`lav`, configurations `lcc` (last committed) and `lac`
(last accepted), `electionWon`, `startedJoinSinceLastReboot`, join and publish votes, last published version `lpv` and
configuration `lpc`.

**Publications** (design 1: P1, P2, P4–P7).

- `pub_wf` (P1): every publication is sent by an eligible node, has term ≥ 1, a parent of term at most its term and
  of strictly smaller version, and, if the parent has term 0, a bootstrap configuration as last committed
  configuration. Term ≥ 1 makes the Zen1 compatibility branch of `handlePublishRequest` dead; the parent order makes
  versions increase along descent.
- `pub_parent` (P1, P5): a parent of term ≥ 1 is the key of a sent publication `Q`, and the configurations follow the
  reconfiguration discipline. Design 1 names its two rules R1 and R2 (not to be confused with the response facts R1,
  R2 below): (R1) the last committed configuration is `Q`'s last committed one, or `Q`'s last accepted one if `Q` is
  committed; (R2) the last accepted configuration differs from `Q`'s only if the last committed configuration is `Q`'s
  last accepted one. R2 is `handleClientValue`'s guard "only allow reconfiguration while not already reconfiguring"
  (CS:387-391); R1 is the asserted copying of the committed configuration (CS:397-398) together with `markCommitted`.
- `pub_unique` (P2): two publications with the same key are the same message (source, state, parent). Keys name
  publications, and a key has one parent.
- `pub_rooted` (no design label): every publication descends from a key of term 0. Versions are integers, so
  "induction on the version" is unavailable; this field makes every chain of ancestors finite, and every induction
  along a branch runs on the `Descends` derivation it provides.
- `pub_same_term` (P4): two publications of the same term are related by descent (a term's publications form a chain).
- `pub_voters` (P6): the eligible nodes that sent the publisher a join of the publication's term include a quorum of
  both of its configurations. Used to show that a node holding such a quorum in that term is the publisher.
- `pub_election` (P7): a publication whose parent is of an older term (the first of its term) carries an election
  record of its publisher for its term, over the parent, with its own last committed configuration as `x`. This is
  where the history of elections is kept without ghost state: the joins are in the soup.

**Commits** (C1).

- `commit_quorum` (C1, weakened for D1): every commit is of a sent publication `C` whose publish responses from
  eligible nodes include a quorum `A` of `C`'s last accepted configuration such that `A` is also a quorum of `C`'s last
  committed configuration, or else `C`'s parent is committed and is a publication with the same last accepted
  configuration as `C`. The second alternative is the D1 case (finding 1); TLA+ has only the first.

**Joins and publish responses** (J1–J3, R1–R2).

- `join_wf` (no design label): every join is from the `DiscoveryNode` of its source's id and is addressed to an
  eligible node.
- `join_term_le` (J1): an eligible node's joins have terms at most its current term.
- `join_unique` (J2): an eligible node sends at most one join per term. A common voter of two elections of one term
  therefore names one candidate.
- `join_after_response` (J3): if an eligible node sent a publish response for `(t', v')` and a join for a term later
  than `t'`, the join's last accepted (term, version) is at least `(t', v')`: it accepted before it voted. This is the
  promise that makes leader completeness work.
- `response_le` (R1): an eligible node's publish responses have terms at most its current term and keys at most its
  last accepted key.
- `response_published` (R2): every publish response answers a publication of its key sent by the node it is
  addressed to.

**Nodes** (N1–N4, N6–N10, and N3r).

- `localNode_eq` (no design label): every node's `localNode` is `P.dn n` (joins carry it).
- `idle_of_not_won` (N4): a node that has not won has last published version 0 and no publish votes.
- `won_started` (N2): a node that has won has handled a start-join since its last restart.
- `votes_started` (N6): a node that holds join votes has handled a start-join since its last restart.
- `started_term_pos` (N10): such a node is in a term ≥ 1.
- `won_quorum` (N3): the join votes of a node that has won are a quorum of its `lcc` and of its `lac`.
- `not_won_no_quorum` (N3r: for the default strategy, the reverse half of `invariant()`'s second assertion; it omits
  the strategy's additional constraint, so for other strategies it is stronger than that half, and `Inv` never
  mentions the strategy; optional in design 1, needed here for `javaInvariant_reachable`): the join votes of a node
  that has not won are not a quorum of both.
- `joinVotes_sent` (N8): every join vote a node holds is of an eligible node that sent it a join for its current term,
  with a last accepted (term, version) `Below` the node's.
- `publishVotes_sent` (N9): every publish vote a node holds is of an eligible node that sent it a publish response for
  (its current term, its last published version).
- `term_le` (N1): an eligible node's last accepted term is at most its current term.
- `accepted_realizes` (N7): an eligible node's accepted state has term 0 and empty configurations (never
  bootstrapped), or its configurations realize its key. Nothing else of the state (payload, metadata version,
  cluster-manager node, UUID flags) is related to the publication, since a restart may rebuild it.

**Leaders** (L1–L5).

- `won_unique` (L1): `Won P W a t` and `Won P W b t` imply `a = b`.
- `pub_source_term` (L2): a node that published in a term is past that term, or still in it and either still elected
  or restarted since; it cannot win that term again.
- `leader_pubs` (L3): every publication of an elected node's current term has a version at most its last published
  version, descends to (current term, last published version), and has both configurations with a quorum in the
  node's join votes.
- `leader_inflight` (L4): an elected node with a publication in flight (`lpv ≠ lav`) sent a publication of key
  (current term, `lpv`) with its accepted key as parent; its `lpc` is that publication's last accepted configuration;
  and its `lcc` is that publication's last committed configuration, or (D1: it applied the commit of its accepted
  state meanwhile) that publication's last accepted configuration, its accepted key being committed with the same last
  accepted configuration.
- `leader_settled` (L5): an elected node with no publication in flight (`lpv = lav`) has `lat` = current term and
  `lpc = lac`, or an older `lat` while no publication of its current term exists.

### Design labels not present, and other differences

- P3 (one source per term) is `one_master_per_term`, a consequence of L1. N5 (votes come from eligible nodes) is
  folded into N8 and N9. N11 (empty `lastPublishedConfiguration` before bootstrap) is part of the bootstrap step's
  contract. Design 1's optional C2 (a commit's source is the publication's source) and J4 (a join's last accepted term
  is below its term) are not needed.
- Design 1 has a single bootstrap configuration and one root ⊥, treated as committed. Here several bootstrap
  configurations are allowed: a term-0 base is realized by `(X, X)` with `P.initConfs X`, a root publication carries a
  bootstrap configuration (`pub_wf`), and where design 1 intersects two quorums of the one configuration, the proofs use
  `P.InitCompatible`. `Committed` is never true at term 0, so the D1 alternatives of C1 and L4 refer to real commits.
- P7 is stated as an `ElectionRecord`, the same shape as the record of a node that has just won, so that election
  leader completeness and election-quorum intersection are proved once for both (design 2's election situations).
- `pub_rooted` replaces strong induction on versions (versions are integers).
- The nine step theorems, `reachable_inv` and the nine public statements about reachable clusters assume the default
  election strategy, and `commit_reachable` exhibits it; the 22 static lemmas, `inv_init` and `bootstrap_compatible`
  do not mention it, and neither does `Inv`. Only `inv_join` and `javaInvariant_reachable` use it: the other step
  theorems leave it unused, `reachable_inv` passes it to the step theorems, and the other public statements pass it on
  to `reachable_inv`.

## Proof architecture

### Consequences of the invariant inside one cluster (`Sol_OpenSearchSafety_static_all.lean`, 22 theorems)

Nothing here mentions steps. In dependency order:

- **The tree.** `descends_trans`; `inv_descends_key` (along a descent the term does not decrease and the version
  strictly increases, so descent is antisymmetric); `inv_descends_parent` (a proper ancestor of a publication is an
  ancestor-or-self of its parent, by `pub_unique`); `inv_descends_linear` (the ancestors of a key form a chain);
  `inv_reign_first` (every publication descends from a first publication of its term).
- **Basic facts.** `inv_committed_published` (a committed key is a publication of term ≥ 1); `inv_eligible_of_won`,
  `inv_won_of_electionWon`.
- **Committed keys along a branch.** `inv_deepest_committed` (the deepest committed ancestor-or-self of any key, or
  none); `inv_first_committed` (the first committed key of a committed key's branch); `inv_first_committed_after` (the
  committed key closest to `d` strictly after it on the way to a committed descendant).
- **Configurations along a branch.** `inv_lineage`, the *path summary* (design 1's Lemma S, design 2's lineage lemma
  L3): between a publication `D` and a descendant `E` with no committed key strictly between, `D`'s last accepted
  configuration is `E`'s last committed or last accepted configuration; at most one reconfiguration is in flight
  relative to the last committed configuration of the branch. `inv_root_lcc` (without a committed proper ancestor the
  last committed configuration is a bootstrap configuration); `inv_commit_quorum_after` (design 1's EC: the
  responders to the committed key closest above `D` include a quorum of `D`'s last accepted configuration, including in
  the D1 case); `inv_commit_quorum_first` (the responders to a first committed key include a quorum of a bootstrap
  configuration); `inv_pivot` (the *pivot* of a realized base: its deepest committed ancestor-or-self carries `x` or `y`
  as last accepted configuration, or nothing is committed below the base and `x` is a bootstrap configuration);
  `inv_pub_lcc` (every publication's last committed configuration is a bootstrap configuration or the accepted
  configuration of a committed publication).
- **Elections.** `inv_elc`, *election leader completeness* (design 2's L6, the core of design 1's Theorem LC): the
  base of every election record of term `t` descends from every committed key of an older term. Strong induction on
  `t`. The induction hypothesis gives leader completeness for publications of terms below `t` (through their first
  publications and `pub_election`) and hence the comparability of committed keys below `t`. A step called `finish`
  shows that a committed key `C'` of an older term to which some voter of the record responded is an ancestor of the
  base: the voter's join is `Below` the base and, by J3, at least `C'`; leader completeness below `t` (older term) or
  `pub_same_term` (same term) concludes. Then, by `inv_pivot`: (I) if the base has a committed pivot `D`, either the
  committed key is below `D`, or the first committed key `C'` after `D` towards it has responders forming a quorum of
  `D`'s last accepted configuration, of which the voters are also a quorum; the common voter puts `C'` below the base,
  hence below `D` by maximality, contradicting antisymmetry. (II) If nothing is committed below the base, the first
  committed key of the committed key's branch has responders forming a quorum of a bootstrap configuration, the voters
  are a quorum of the bootstrap configuration `x`, `P.InitCompatible` gives a common voter, and `finish` gives a
  committed ancestor of the base, a contradiction. `inv_leader_completeness` and `inv_committed_comparable` follow.
  `inv_election_quorums` (design 1's ESL, design 2's L8): two election records of one term share a voter, because
  their bases have the same pivot (by `inv_elc` in both directions) or both have none (then `P.InitCompatible`).
  `inv_election_unique`: they have the same candidate, by J2.

### Preservation (`Sol_OpenSearchSafety_steps_all.lean`, 10 theorems)

`inv_init`, then one theorem per `Step` constructor with the constructor's hypotheses, `Inv P W`, `P.InitCompatible`
and the default strategy, concluding `Inv P W'`. Private infrastructure at the top of the file: cluster updates
(`set_node_self`, `set_node_ne`), monotonicity of every soup-only notion under sending (`committed_mono`,
`descends_mono`, `realizes_mono`, `joinVoters_mono`, `baseVoters_mono`, `respVoters_mono`, `electionRecord_mono`),
quorum facts (`quorum_intersect`, `quorum_mono`, `hasQuorum_nil`, `addVote_mem`), the handlers' effects as record
equations (`spec_setInitialState`, `spec_startJoin`, `spec_join`, `spec_clientValue`, `spec_publish`, `spec_respond`,
`spec_commit`), `markCommitted_spec` and `vomv_of_pos`. Each proof derives the changed fields of the node, describes
the new messages, shows that winning only shrinks (or, for `join`, how it grows), and builds the 30 fields by cases on
whether the node concerned is the one that stepped.

- `inv_bootstrap`, `inv_startJoin`, `inv_restart`, `inv_restartAny`: local. A node with accepted term 0 has sent no
  publish response (`response_le`, `response_published`, `pub_wf`), which covers bootstrapping and the restart of a
  node that never joined; the new join of `startJoin` carries the node's version (its accepted term is ≥ 1 if it ever
  responded, `vomv_of_pos`), which gives J3.
- `inv_join`: the only step that needs the election lemmas. When the join wins the election, the node's accepted term
  is older than its current term, its votes form an election record, no publication of its term exists, and no other
  node has won the term; the last two by `inv_election_unique` against the record of the term's first publication
  (`inv_reign_first`, `pub_election`) or of another elected node (`leader_settled`), combined with `pub_source_term`.
- `inv_clientValue`: the new publication's parent is the leader's accepted key, which its configurations realize; the
  earlier publications of the term descend to it (`leader_settled`, `leader_pubs`); the leader's join votes give
  `pub_voters` and `pub_election`.
- `inv_publish`: the accepted key strictly increases (term ≥ 1 rules out the Zen1 branch); an elected node accepts
  exactly its own publication in flight; a node that has not won cannot hold a quorum of the new configuration
  (`pub_voters`, J2, L2).
- `inv_respond`: a new commit's record (C1) from the publish votes, with the D1 alternative supplied by
  `leader_inflight`, or the record of an earlier commit of the same key.
- `inv_commit`: the D1 case of `leader_inflight` (finding 1) and `not_won_no_quorum` after the configuration change.

### Assembly (`Sol_OpenSearchSafety_all.lean`, 12 theorems)

`reachable_inv` by induction on `Reachable` (one preservation theorem per step). Each safety statement is then a
consequence of `Inv` and the static lemmas. `bootstrap_compatible` is a counting argument independent of the
cluster. `commit_reachable` exhibits a six-step execution of a one-node cluster.

### Checks

- `lake build Definitions.Def_OpenSearchSafety`; `lake env lean` on each of the three `_all` files: no messages.
- The split files import the other theorems only through the `Theorems/` stubs (`sorry` by design); their
  `import Theorems.Thm_OpenSearchSafety_...` lines fix the order of `ORDER` in the items file (checked: each theorem
  comes after every theorem whose stub its file imports).
- End to end without stubs (the three files concatenated into one module, the duplicated private lemmas renamed, then
  `#print axioms` for the 44 theorems): no `sorry`; 39 theorems depend on `propext`, `Classical.choice` and
  `Quot.sound`, `inv_committed_published` and `commit_reachable` on `propext` and `Quot.sound`, and `descends_trans`,
  `inv_descends_parent` and `inv_descends_linear` on no axiom. No `native_decide`, `bv_decide` or custom syntax.

## Validation by model checking

Before the Lean proof, two invariants were designed independently, each with an explicit-state model checker of the
same message-soup model with the Java semantics: the step kinds above, the differences D1–D7 between the Java and the
TLA+ model (`HandleCommit` guard, eligibility of voters, `versionOrMetadataVersion`, the Zen1 branch, the cluster-UUID
flag, the election-strategy extension point, the publish quorum read from the current state), the ghost parent, and
arbitrary term-0 initial states. The checkers bootstrap every node with a single configuration and restart nodes with
their persisted state intact; several bootstrap configurations and arbitrary restarts of nodes that are not eligible
were added to the model afterwards and are covered by the proof only.

- **Design 1** (ballot style, about 35 conjuncts labelled P, C, J, R, N and L). A Python checker. About 29 million
  states explored by breadth-first search, exhaustive up to a depth of 7 to 22 steps depending on the bounds and role
  restrictions (one D1-focused instance exhausted completely: 96,021 states); about 6 million steps of guided random
  executions (4 and 5 nodes, terms up to 12, reconfiguration families including disjoint configurations, a node that
  is not eligible, stale candidates, D1 interleavings, partial deliveries, restarts). Inductiveness spot-check: about
  280,000 worlds satisfying the invariant but not reached from the seeds, about 39 million successor steps (including
  about 18,000 election wins and about 500 D1 commits), 0 counterexamples to induction.
- **Design 2** (configuration lineage, 23 components). A Python reference model and a C++ port, cross-validated
  (identical state counts on four instances). About 1.33 billion states in C++ depth-first runs with bit-state hashing,
  two of them complete: 25.4 million states (4 nodes, terms ≤ 2, versions ≤ 2, at most 8 messages) and 201.1 million
  states (4 nodes, terms ≤ 3, versions ≤ 2, at most 7 messages, 85,538 states with a committed reconfiguration, 24
  D1 transitions); 3.7 million states by exact breadth-first search in Python; random walks of 33.2 million (C++) and
  3.2 million (Python) steps, with about 400,000 elections, 29,000 committed reconfigurations and 12,000 D1 events.
  Inductiveness spot-check: 9.4 million worlds satisfying the invariant, 149 million successor steps, 0 counterexamples
  to induction; the check is not vacuous (dropping some components yields counterexamples to induction within
  minutes, dropping C1 yields worlds violating the total order of commits).

Bounded checking is evidence, not proof (bit-state hashing may omit states; the spot-checks mutate worlds near reached
ones). The Lean invariant follows design 1's conjuncts, uses design 2's lineage lemma and election situations, and is
proved inductive (for compatible bootstrap configurations and the default election strategy) for every cluster size and
every execution.

## Findings

1. **TLA+'s `CommitHasQuorumVsPreviousCommittedConfiguration` fails for the Java semantics (D1).** TLA+'s
   `HandleCommit` has the guard `electionWon ⇒ lastAcceptedVersion = lastPublishedVersion` (ZenWithTerms.tla:246);
   Java's `handleCommit` (CS:523-573) does not. A cluster-manager can therefore apply the commit of its accepted state
   while its next publication is in flight, and since `isPublishQuorum` reads the last committed configuration of the
   current accepted state (CS:156-158), that publication can then be committed with a quorum of the new configuration
   only. The TLA+ invariant (for every commit and every publication of the same key, the senders of publish responses
   for that key are a quorum of the publication's last committed configuration) fails. Shortest execution, found by
   exhaustive search in both designs (17 steps; design 2's version; nodes 1–4, all eligible, bootstrap configuration
   {1,2,3}):
   1. node 1 bootstraps with {1,2,3};
   2. nodes 1, 2 and 4 handle a start-join from node 1 for term 1 (steps 2–4);
   3. node 1 handles the joins of nodes 1 and 2 and wins term 1 with votes {1,2} (steps 5–6);
   4. node 1 publishes (1,1) with last committed configuration {1,2,3} and last accepted configuration {1,2,4}, a
      reconfiguration, allowed because its two configurations are equal and {1,2} is a quorum of {1,2,4} (step 7);
   5. nodes 1 and 2 accept (1,1), and node 1 handles both responses: {1,2} is a quorum of {1,2,3} and of {1,2,4}, so
      the commit of (1,1) is sent (steps 8–11);
   6. node 1 publishes (1,2) with configurations {1,2,3} and {1,2,4}: its accepted configuration may not change while
      its two configurations differ (step 12);
   7. node 1 applies the commit of (1,1); its accepted state is still (1,1), so Java accepts the commit (TLA+ would
      not), and node 1's last committed configuration becomes {1,2,4} (step 13);
   8. node 2 accepts (1,2) and node 1 handles its response; node 4, which never bootstrapped (`handlePublishRequest`
      does not require it), accepts (1,2), and node 1 handles its response: the publish votes {2,4} are a quorum of
      node 1's current last committed configuration {1,2,4} and of the published {1,2,4}, so the commit of (1,2) is
      sent (steps 14–17).

   The responders to (1,2), nodes 2 and 4, are not a quorum of (1,2)'s last committed configuration {1,2,3}. Safety
   is unaffected: the parent (1,1) is committed with last accepted configuration {1,2,4}, equal to (1,2)'s, and
   {2,4} is a quorum of it. The invariant's commit fact `commit_quorum` has exactly this second alternative, and
   `leader_inflight` records the cluster-manager's state after such a commit; `inv_commit_quorum_after` shows that the
   weaker fact still meets every election quorum. Design 1 found an equivalent 17-step execution with node 2 as
   cluster-manager and the reconfiguration {1,2,3} to {2,3,4}. Whether the `Coordinator` can produce this interleaving
   was not analysed (it runs one publication at a time, and the cluster-manager normally handles the commit of its own
   publication before that publication completes); it is reachable at the level of `CoordinationState`, the level of
   the TLA+ model, and the invariant covers it.

2. **A cluster-manager's last committed configuration can move backwards (design 2).** Take steps 1–13 above without
   node 4: node 1's last committed configuration has become {1,2,4}. Then node 1 accepts its own publication (1,2),
   whose last committed configuration is {1,2,3} (the configuration node 1 had when it published), and its last
   committed configuration is {1,2,3} again. TLA+'s guard prevents this. No fact of the invariant assumes that a node's
   last committed configuration is monotone; `leader_inflight` lists its two possible values.

3. **A non-monotone election strategy breaks "one state per term and version" when Java assertions are off.** An
   election strategy plugin (`DiscoveryPlugin.getElectionStrategies()`, selected per node by
   `cluster.election.strategy`) adds a condition `satisfiesAdditionalQuorumConstraints` to the election quorum.
   `handleJoin` recomputes `electionWon` from scratch at each join; that a won election stays won is only an assertion
   (CS:323-324), and a transition from lost to won sets `lastPublishedVersion` to the last accepted version. With the
   strategy "the number of join votes is not 3" (design 2, 11 steps; nodes 1–4, bootstrap configuration {1,2,3}):
   node 1 bootstraps (1); nodes 1–4 handle a start-join from node 1 for term 1 (2–5); node 1 handles the joins of
   nodes 3 and 1 and wins with 2 votes, last published version 0 (6–7); node 1 publishes (1,1) with value 0 (8);
   node 1 handles node 2's join: 3 votes, the strategy fails, `electionWon` becomes false (the assertion would fail
   here; without assertions the last published version stays 1) (9); node 1 handles node 4's join: 4 votes, it wins
   again and its last published version is reset to its last accepted version, 0, since it has not accepted (1,1)
   (10); node 1 publishes a second, different (1,1) with value 1 (11). `one_state_per_version` fails, and so do TLA+'s
   `LogMatching` and Java's `invariant()`. Design 1 found a 12-step variant with five nodes. OpenSearch at this
   revision ships only `ElectionStrategy.DEFAULT_INSTANCE`, the constant `true`, and the theorems assume it. The designs
   argue, without a Lean proof, that the invariant also holds for any strategy satisfying the assertion as a contract
   (design 2) or monotone in the votes and independent of the accepted state (design 1).

4. **TLA+'s `CommittedValuesDescendantsFromInitialValue` fails (D3), harmlessly.** Java's joins and pre-vote responses
   of a term-0 state carry its metadata version, and `handleJoin` compares it with the candidate's metadata version.
   Design 1's execution: nodes 1–3, bootstrap configuration {1,2,3}; initially node 1 has version 0 and metadata
   version 5, nodes 2 and 3 version 3 and metadata version 1. Node 1 bootstraps; nodes 1 and 2 handle a start-join from
   node 1 for term 1; node 1 handles its own join and node 2's, accepted because 1 ≤ 5, and wins; it publishes (1,1)
   with parent (0,0); nodes 1 and 2 accept, and node 1 commits (1,1). The TLA+ invariant asks for an initial version
   `v` such that some quorum of the initial configuration has initial versions at most `v` and every committed
   publication descends from `(0, v)`; (1,1) descends only from (0,0), and only node 1 has an initial version ≤ 0. The
   proof needs only that a base of term 0 forces joins of term 0 (`Below` ignores versions at term 0), and nothing is
   lost for safety.

5. **OpenSearch's randomized test.** `CoordinationStateTests.testSafety` (CoordinationStateTests.java:917-924) runs
   `CoordinationStateTestCluster.runRandomly` (test/framework, CoordinationStateTestCluster.java:279-329) on 1 to 5
   nodes with the default strategy: start-joins of random terms, bootstraps, reboots, client values with random terms,
   versions and configurations, and random deliveries from a message list that is never emptied. It checks the
   assertions of `invariant()` at every node after each iteration, and at the end the first two properties: one
   cluster-manager per term and one cluster state per term and version (CoordinationStateTestCluster.java:331-370).
   For every execution of the model with compatible bootstrap configurations and the default strategy (the test uses a
   single bootstrap configuration and the default strategy), `one_master_per_term` and `one_state_per_version` prove the
   two properties checked at the end, and `javaInvariant_reachable` the assertions of `invariant()` at every
   cluster-manager-eligible node; the test checks these assertions at every node, and in the model a node that is not
   eligible may restart with any persisted state, which can break the first assertion. Two observations on the test:
   - The branch of `reboot()` that makes a node that is not cluster-manager-eligible lose its persisted state
     (CoordinationStateTestCluster.java:157-169) has had no effect since the introduction of `PersistedStateRegistry`:
     it assigns a new `InMemoryPersistedState` to the node's `persistedState` field, but the rebooted
     `CoordinationState` reads its persisted state from the registry (line 192), where the original was registered
     once in the constructor (line 150), and `addPersistedState` is `putIfAbsent` (PersistedStateRegistry.java:38-41).
     The test therefore no longer exercises state loss. The model does: `restartAny`.
   - `reboot()` also toggles the cluster-manager role (lines 171-178), keeping the persisted state; the model fixes
     roles.

## Assumptions

Outside the model, as listed in the docstring of `Def_OpenSearchSafety.lean`:

- **Roles are fixed.** A node's cluster-manager role never changes. Changing it and back can reset the persisted term:
  a node started without the cluster-manager and data roles overwrites its persisted state with term 0 and an empty
  cluster state (GatewayMetaState.java:232-255), so, once eligible again, it could send a second join in a term in
  which it had already sent one. A node that keeps the data role but loses the cluster-manager role switches to
  asynchronous persistence (GatewayMetaState.java:199-206).
- **No disk rollback.** The persisted term and accepted state of an eligible node survive every restart exactly as
  `RestartState` describes.
- **No offline tools.** The `opensearch-node` commands (`unsafe-bootstrap`, `detach-cluster`, `remove-settings`,
  `remove-customs`) rewrite the persisted state and are not modelled.
- **Bootstrap requirements resolve consistently.** Each requirement names the same node at every node, as
  `bootstrap_compatible` requires; the theorems themselves assume `P.InitCompatible`.
- **One election strategy, the default.** The statements about reachable clusters, `reachable_inv` and the step theorems
  assume `P.strategy = ElectionStrategy.DEFAULT_INSTANCE` for every node (finding 3).
- **Remote publication is exact.** A publication delivered through the remote cluster-state store reconstructs exactly
  the published state. The REMOTE persisted state is omitted, as in the per-node mission.
- **The per-node abstractions** of `OpenSearchCoordination` (terms are naturals, versions integers without overflow,
  the reduced cluster state, voter ids only, rejections as values) and its treatment of assertions.

## What is not proved

- **Liveness.** Nothing here says that an election eventually succeeds, that a publication is eventually committed, or
  how long anything takes. Other missions cover it: `OpenSearchPreVote` (what a single pre-voting round guarantees),
  `OpenSearchProgress` (over the same cluster model, an election or a publication that nothing disrupts succeeds), and
  `OpenSearchElectionTimer` (probability bounds on rounds in which randomized election timers collide).
- **The `Coordinator`.** Its calls are argued, not proved, to be steps of the model; mode changes, the publication
  pipeline and its timeouts, `LagDetector`, `FollowersChecker`, `LeaderChecker`, join validation, the `Reconfigurator`
  and voting-configuration exclusions are not transcribed.
- **Anything outside the assumptions**: role changes, state loss or rollback at eligible nodes, the offline tools,
  incompatible bootstrap configurations (including the best-effort bootstrap without discovery settings), plugin
  election strategies, the remote cluster-state store.
- **`invariant()` at nodes that are not eligible**, which may restart with any persisted state.
- **The applied state.** The theorems are about publications and commits sent; that nodes apply committed states in
  order, and what they serve to clients, is outside the model.
- **The Java runtime**: concurrency inside a node, I/O failures, `long` overflow.
