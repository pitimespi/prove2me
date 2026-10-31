# Read-back: `Def_OpenSearchSafety.lean`

This file imports `Definitions.Def_OpenSearchCoordination` and introduces, in the namespace `OpenSearchSafety` (with `OpenSearchCoordination` opened), 25 declarations, in this order: the message type `Message`; the parameters `Params`, with `Params.dn` and the condition `Params.InitCompatible`; the predicate `BootstrapConfig`; the cluster type `Cluster` with the updates `Cluster.set` and `Cluster.send`; `Initial`, `RestartState`, the step relation `Step` and `Reachable` (together, the *model*); the relations `Committed`, `Parent` and `Descends` on (term, version) pairs; and, under the heading "The inductive invariant", the proof-side notions `KeyLE`, `Below`, `Published`, `Realizes`, `JoinVoters`, `BaseVoters`, `RespVoters`, `ElectionRecord`, `Won` and the 30-field invariant `Inv`. The imported notions are expanded first so that each declaration can be read on its own. Java line citations were checked against the local OpenSearch checkout, whose `HEAD` is the cited revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`.

## Imported notions, expanded

**Node ids and discovery nodes.** A node id is a natural number (Java: a string; only equality is used). A *discovery node* is a pair (id $\in \mathbb{N}$, cluster-manager flag $\in \mathrm{Bool}$); two discovery nodes are equal iff both components are equal. $\mathrm{ZEN1\_BWC\_TERM} = 0$.

**Voting configurations.** A voting configuration $c$ is a list $c.\mathrm{nodeIds}$ of node ids together with a proof that the list is strictly increasing. It therefore has no duplicates, and two configurations are equal iff their lists are equal, i.e. iff they contain the same ids. $\mathrm{EMPTY}$ is the configuration with the empty list; $c$ is *empty* iff its list is empty. For a list $q$ of node ids,
$$c.\mathrm{hasQuorum}(q) \iff 2\cdot\big|\{x \in c.\mathrm{nodeIds} : x \in q\}\big| > |c.\mathrm{nodeIds}|,$$
the count ranging over the (duplicate-free) members of $c$: strictly more than half of the members of $c$ occur in $q$. Members of $q$ outside $c$, the order of $q$ and repetitions in $q$ are irrelevant, and $\mathrm{EMPTY}$ has no quorum (not even of $[\,]$, since $0 > 0$ fails). Below, "$q$ is a quorum of $c$" means $c.\mathrm{hasQuorum}(q)$.

**Vote collections.** A vote collection is a list of node ids (most recent first); the empty collection is $[\,]$. For a discovery node $\delta$, $\mathrm{addVote}(v, \delta)$ is $(\delta.\mathrm{id} :: v,\ \mathrm{true})$ if $\delta$'s cluster-manager flag is true and $\delta.\mathrm{id} \notin v$, and $(v,\ \mathrm{false})$ otherwise; so a vote from a node whose flag is false is never recorded, and a node is recorded at most once. A collection $v$ is a quorum of $c$ iff $c.\mathrm{hasQuorum}(v)$; it contains a vote for $\delta$ iff $\delta.\mathrm{id} \in v$; it is empty iff $v = [\,]$.

**Cluster states.** A cluster state $s$ over a payload type $V$ has nine fields: $s.\mathrm{term} \in \mathbb{N}$; $s.\mathrm{version} \in \mathbb{Z}$; $s.\mathrm{metadataVersion} \in \mathbb{Z}$; configurations $s.\mathrm{lcc}$ (last committed) and $s.\mathrm{lac}$ (last accepted); $s.\mathrm{cmn}$, the cluster-manager node, which is "none" or "some $m$" with $m \in \mathbb{N}$; Booleans $s.\mathrm{uuidKnown}$ and $s.\mathrm{uuidCommitted}$; and a payload $s.\mathrm{value} \in V$. Its *key* is the pair $(s.\mathrm{term}, s.\mathrm{version}) \in \mathbb{N} \times \mathbb{Z}$. $\mathrm{vomv}(s)$ ("version or metadata version") is $s.\mathrm{metadataVersion}$ if $s.\mathrm{term} = 0$ and $s.\mathrm{version}$ otherwise. $\mathrm{markCommitted}(s)$ is $s$ with $s.\mathrm{lcc}$ replaced by $s.\mathrm{lac}$ (no change if they are already equal) and then, if $s.\mathrm{uuidKnown}$ is true and $s.\mathrm{uuidCommitted}$ is false, $s.\mathrm{uuidCommitted}$ set to true; every other field is unchanged.

**Message payloads.** A start-join request is a pair (source discovery node, term $\in \mathbb{N}$). A *join* $j$ consists of a source discovery node $j.\mathrm{src}$, a target discovery node $j.\mathrm{tgt}$, a term $j.\mathrm{term} \in \mathbb{N}$, a last accepted term $j.\mathrm{lat} \in \mathbb{N}$ and a last accepted version $j.\mathrm{lav} \in \mathbb{Z}$; equality of joins is equality of all five fields. A publish request wraps one cluster state. A publish response is a pair $(t, v) \in \mathbb{N} \times \mathbb{Z}$. An apply-commit request is a triple (source discovery node, term $\in \mathbb{N}$, version $\in \mathbb{Z}$).

**Election strategies.** An election strategy is a single Boolean function $\mathrm{extra}(\delta, t, at, av, c_1, c_2, \mathit{votes})$ of a discovery node, a current term, an accepted term, an accepted version, two configurations and a vote collection. The default strategy returns true on every input. (`ElectionStrategy.Monotone` is defined in the imported file and not used in this one.)

**Coordination states.** A coordination state $c$ has nine fields: $c.\mathrm{localNode}$, a discovery node; the persisted part $c.\mathrm{currentTerm} \in \mathbb{N}$ and $c.\mathrm{acc}$ (the last accepted cluster state); and the transient part $c.\mathrm{joinVotes}$, $c.\mathrm{started}$ ("started a join since the last reboot"), $c.\mathrm{won}$ ("election won"), $c.\mathrm{lpv} \in \mathbb{Z}$ (last published version), $c.\mathrm{lpc}$ (last published configuration) and $c.\mathrm{publishVotes}$. Derived: $c.\mathrm{lat} = c.\mathrm{acc}.\mathrm{term}$, $c.\mathrm{lav} = c.\mathrm{acc}.\mathrm{version}$, $c.\mathrm{lcc} = c.\mathrm{acc}.\mathrm{lcc}$, $c.\mathrm{lac} = c.\mathrm{acc}.\mathrm{lac}$. The constructor $\mathrm{init}(\delta, t, s)$ is the coordination state with local node $\delta$, current term $t$, accepted state $s$, empty join votes, $\mathrm{started} = \mathrm{won} = \mathrm{false}$, $\mathrm{lpv} = 0$, $\mathrm{lpc} = s.\mathrm{lac}$ and empty publish votes.

$\mathrm{isElectionQuorum}(es, c, \mathit{votes})$ holds iff $\mathit{votes}$ is a quorum of $c.\mathrm{lcc}$, is a quorum of $c.\mathrm{lac}$, and $es.\mathrm{extra}(c.\mathrm{localNode}, c.\mathrm{currentTerm}, c.\mathrm{lat}, c.\mathrm{lav}, c.\mathrm{lcc}, c.\mathrm{lac}, \mathit{votes})$ is true. $\mathrm{isPublishQuorum}(c, \mathit{votes})$ holds iff $\mathit{votes}$ is a quorum of $c.\mathrm{lcc}$ and of $c.\mathrm{lpc}$.

The handlers return either an error or a result; the cluster steps below use only successful calls ("succeeds with"). Guards are tested in the order listed, and the first guard that applies produces the error.

- $\mathrm{setInitialState}(c, s)$: error if $c.\mathrm{lac}$ is non-empty; otherwise succeeds with $c$ with $\mathrm{acc} := s$. Its *contract* $\mathrm{initialStateContract}(c, s)$ (Java assertions, not checked by the handler) is the conjunction: $c.\mathrm{lat} = 0$; $c.\mathrm{lcc}$ empty; $c.\mathrm{lpv} = 0$; $c.\mathrm{lpc}$ empty; $c.\mathrm{won} = \mathrm{false}$; $c.\mathrm{joinVotes}$ empty; $c.\mathrm{publishVotes}$ empty; $s.\mathrm{term} = 0$; $s.\mathrm{version} = c.\mathrm{lav}$; $s.\mathrm{lac}$ non-empty; $s.\mathrm{lcc}$ non-empty.
- $\mathrm{handleStartJoin}(c, (\delta, t))$: error if $t \le c.\mathrm{currentTerm}$; otherwise succeeds with the pair of ($c$ with $\mathrm{currentTerm} := t$, $\mathrm{lpv} := 0$, $\mathrm{lpc} := c.\mathrm{lac}$, $\mathrm{started} := \mathrm{true}$, $\mathrm{won} := \mathrm{false}$, $\mathrm{joinVotes} := [\,]$, $\mathrm{publishVotes} := [\,]$) and the join $(c.\mathrm{localNode},\ \delta,\ t,\ c.\mathrm{lat},\ \mathrm{vomv}(c.\mathrm{acc}))$. The accepted state is unchanged.
- $\mathrm{handleJoin}(es, c, j)$: (1) error if $j.\mathrm{term} \neq c.\mathrm{currentTerm}$; (2) error if $c.\mathrm{started}$ is false; (3) error if $j.\mathrm{lat} > c.\mathrm{lat}$; (4) error if $j.\mathrm{lat} = c.\mathrm{lat}$ and $j.\mathrm{lav} > \mathrm{vomv}(c.\mathrm{acc})$; (5) error if $c.\mathrm{lac}$ is empty; otherwise, with $(\mathit{votes}, \mathit{added}) = \mathrm{addVote}(c.\mathrm{joinVotes}, j.\mathrm{src})$ and $w = \mathrm{isElectionQuorum}(es, c, \mathit{votes})$ (evaluated on $c$'s own terms and configurations, which the call does not change), succeeds with $(c', \mathit{added})$, where $c'$ is $c$ with $\mathrm{joinVotes} := \mathit{votes}$ and $\mathrm{won} := w$, and in addition $\mathrm{lpv} := c.\mathrm{lav}$ when $w$ is true and $c.\mathrm{won}$ was false. The target of $j$ is not checked (Java asserts it), and nothing prevents $\mathrm{won}$ from going from true to false (Java only asserts that it cannot).
- $\mathrm{handleClientValue}(c, s)$: (1) error if $c.\mathrm{won}$ is false; (2) error if $c.\mathrm{lpv} \neq c.\mathrm{lav}$; (3) error if $s.\mathrm{term} \neq c.\mathrm{currentTerm}$; (4) error if $s.\mathrm{version} \le c.\mathrm{lpv}$; (5) error if $s.\mathrm{lac} \neq c.\mathrm{lac}$ and $c.\mathrm{lcc} \neq c.\mathrm{lac}$; (6) error if $c.\mathrm{joinVotes}$ is not a quorum of $s.\mathrm{lac}$; otherwise succeeds with ($c$ with $\mathrm{lpv} := s.\mathrm{version}$, $\mathrm{lpc} := s.\mathrm{lac}$, $\mathrm{publishVotes} := [\,]$; the publish request of $s$). Its contract $\mathrm{clientValueContract}(c, s)$ is $s.\mathrm{lcc} = c.\mathrm{lcc}$.
- $\mathrm{handlePublishRequest}(c, s)$: (1) error if $s.\mathrm{term} \neq c.\mathrm{currentTerm}$; (2) else, if $s.\mathrm{term} = c.\mathrm{lat}$ and $s.\mathrm{version} \le c.\mathrm{lav}$: when $s.\mathrm{term} = 0$, error if $s.\mathrm{cmn}$ is none, accept if $s.\mathrm{cmn} = \text{some } m$ and "some $m$" differs from $c.\mathrm{acc}.\mathrm{cmn}$, error otherwise; when $s.\mathrm{term} \neq 0$, error; (3) otherwise accept. *Accept* means: succeed with ($c$ with $\mathrm{acc} := s$; the response $(s.\mathrm{term}, s.\mathrm{version})$). Transient fields are unchanged.
- $\mathrm{handlePublishResponse}(c, \delta, (t, v))$: (1) error if $c.\mathrm{won}$ is false; (2) error if $t \neq c.\mathrm{currentTerm}$; (3) error if $v \neq c.\mathrm{lpv}$; otherwise, with $\mathit{votes}$ the first component of $\mathrm{addVote}(c.\mathrm{publishVotes}, \delta)$ and $c'$ equal to $c$ with $\mathrm{publishVotes} := \mathit{votes}$, succeeds with $(c',\ \text{some }(c.\mathrm{localNode}, t, v))$ if $\mathit{votes}$ is a quorum of $c.\mathrm{lcc}$ and of $c.\mathrm{lpc}$, and with $(c',\ \text{none})$ otherwise.
- $\mathrm{handleCommit}(c, (\sigma, t, v))$: (1) error if $t \neq c.\mathrm{currentTerm}$; (2) error if $t \neq c.\mathrm{lat}$; (3) error if $v \neq c.\mathrm{lav}$; otherwise succeeds with $c$ with $\mathrm{acc} := \mathrm{markCommitted}(c.\mathrm{acc})$.

(`javaInvariant` is defined in the imported file and not used in this one.)

*Citation check of the imported transcription.* The handlers above, the constructor (CS:84-106), `isElectionQuorum` (CS:144-154 with ES:68-88), `isPublishQuorum` (CS:156-158), `VoteCollection.addVote` (CS:755-757; `handleJoin` calls `addJoinVote`, CS:759-765, which calls `addVote` and only additionally records the join), `VotingConfiguration.hasQuorum`, `isEmpty` and `EMPTY_CONFIG` (CM:405-409, 433-435, 385), `getVersionOrMetadataVersion` (CLS:239-244), `markLastAcceptedStateAsCommitted` with `commitVotingConfiguration` (CS:703-740) and `ZEN1_BWC_TERM` (Coordinator.java:134) were compared with the cited lines and match, guards and their order included, up to the abstractions the imported file declares (remote persisted state omitted, Java assertions turned into contracts, a `null` incoming cluster-manager in the Zen1 branch treated as a rejection).

## Declaration 1: `Message`

`Message V` is an inductive type with four constructors; messages are equal iff they have the same constructor and equal arguments (for publish requests this includes the whole cluster state, payload included).

- `join j`, for a join $j$.
- `publishRequest src s pt pv`, written $\mathrm{PR}(\mathit{src}, s, pt, pv)$: a source node id $\mathit{src}$, a cluster state $s$, and $pt \in \mathbb{N}$, $pv \in \mathbb{Z}$, the *ghost parent* (term, version) (docstring: "with the ghost parent"). A publish request has no addressee.
- `publishResponse src dest r`, written $\mathrm{RESP}(\mathit{src}, \mathit{dest}, (t, v))$ for $r = (t, v)$: a response from node id $\mathit{src}$ to node id $\mathit{dest}$.
- `applyCommit c`, written $\mathrm{AC}(\sigma, t, v)$ for $c = (\sigma, t, v)$; the source $\sigma$ is a discovery node. It has no addressee.

Start-join requests are not messages of the model.

## Declaration 2: `Params`

A structure with three fields: $P.\mathrm{eligible} : \mathbb{N} \to \mathrm{Bool}$ (docstring: `DiscoveryNode.isClusterManagerNode()` of each node; it is fixed for the whole execution); $P.\mathrm{initConfs}$, an arbitrary predicate on voting configurations, "the configurations a node may bootstrap with" (it may be empty, a single configuration, or infinitely many); and $P.\mathrm{strategy}$, one election strategy used by every node. Below, $E(x)$ abbreviates $P.\mathrm{eligible}(x) = \mathrm{true}$ ("$x$ is eligible").

## Declaration 3: `Params.dn`

$P.\mathrm{dn}(n)$ is the discovery node $(n,\ P.\mathrm{eligible}(n))$.

## Declaration 4: `Params.InitCompatible`

$P.\mathrm{InitCompatible}$ is the proposition: for all configurations $X, Y$ with $P.\mathrm{initConfs}(X)$ and $P.\mathrm{initConfs}(Y)$, and all lists $q_1, q_2$ of node ids all of whose members are eligible,
$$X.\mathrm{hasQuorum}(q_1) \wedge Y.\mathrm{hasQuorum}(q_2) \;\Rightarrow\; \exists x,\ x \in q_1 \wedge x \in q_2 .$$
$X = Y$ is included, but for $X = Y$ the implication holds automatically (two sets of members of $X$, each of more than half its size, intersect), so the condition constrains only pairs of distinct bootstrap configurations. It holds trivially when $P.\mathrm{initConfs}$ has at most one element. A configuration with no eligible member has no eligible quorum and so imposes nothing. The docstring ("votes of cluster-manager-eligible nodes that form a quorum of one bootstrap configuration share a voter with votes that form a quorum of another") matches. This condition is not used by the model; it appears only as a hypothesis of theorems.

## Declaration 5: `BootstrapConfig`

For $k \in \mathbb{N}$, functions $\mathrm{resolve}, \mathrm{placeholder} : \mathbb{N} \to \mathbb{N}$, $\mathrm{matched} : \mathbb{N} \to \mathrm{Bool}$ and a configuration $X$, $\mathrm{BootstrapConfig}(k, \mathrm{resolve}, \mathrm{placeholder}, \mathrm{matched}, X)$ is the conjunction of

1. for every node id $x$: $x \in X.\mathrm{nodeIds} \iff \exists i < k,\ x = \big(\text{if } \mathrm{matched}(i) \text{ then } \mathrm{resolve}(i) \text{ else } \mathrm{placeholder}(i)\big)$;
2. $2 \cdot \big|\{ i < k : \mathrm{matched}(i) \}\big| > k$.

So $X$ is exactly the set of the $k$ contributions (requirement $i$ contributes $\mathrm{resolve}(i)$ if matched and $\mathrm{placeholder}(i)$ otherwise), and strictly more than half of the requirement indices are matched; in particular $k \ge 1$. Left unconstrained: $\mathrm{resolve}$ and $\mathrm{placeholder}$ need not be injective and their images need not be disjoint, so $X$ may have fewer than $k$ members and the matched count need not equal the number of distinct resolved ids; nothing is said about the eligibility of any id; nothing requires the bootstrapping node to be among the resolved ids. This predicate is not referenced by any other declaration of the file; in particular the `bootstrap` step uses $P.\mathrm{initConfs}$, and nothing in this file links the two.

*Citation check.* CBS:176-215 (`onFoundPeersUpdated`) bootstraps only if `nodesMatchingRequirements.size() * 2 > bootstrapRequirements.size()`; CBS:259-273 (`startBootstrap`) forms the configuration from the ids of the matching nodes and `"{bootstrap-placeholder}-" + requirement` for each unsatisfied requirement; CBS:306-335 (`checkRequirements`) cancels bootstrapping if a requirement matches several nodes or a node matches several requirements. The Lean predicate matches the counting and the shape of the configuration. The Java code additionally requires the local node to be cluster-manager-eligible and among the matching nodes (CBS:179, 202-209) and guarantees the injectivity that the Lean leaves open; Java's best-effort bootstrap without configured requirements (`scheduleUnconfiguredBootstrap`, CBS:217-250) is not described by this predicate.

## Declaration 6: `Cluster`

`Cluster V` is a structure with two fields: $W.\mathrm{node} : \mathbb{N} \to$ coordination states (one for **every** natural number), and $W.\mathrm{sent}$, a predicate on messages ("has been sent"). For an arbitrary cluster, $W.\mathrm{sent}$ is an arbitrary, possibly infinite, set of messages.

## Declaration 7: `Cluster.set`

$W.\mathrm{set}(n, cs)$ is $W$ with node $n$'s state replaced by $cs$: its node function maps $m$ to $cs$ if $m = n$ and to $W.\mathrm{node}(m)$ otherwise; $\mathrm{sent}$ is unchanged.

## Declaration 8: `Cluster.send`

$W.\mathrm{send}(m)$ is $W$ with $\mathrm{sent}$ replaced by $x \mapsto W.\mathrm{sent}(x) \vee x = m$; the node states are unchanged.

## Declaration 9: `Initial`

$\mathrm{Initial}(P, W)$ is the conjunction of

1. for every node $n$ there is a cluster state $s$ with $s.\mathrm{term} = 0$, $s.\mathrm{lcc} = \mathrm{EMPTY}$, $s.\mathrm{lac} = \mathrm{EMPTY}$ and $W.\mathrm{node}(n) = \mathrm{init}(P.\mathrm{dn}(n), 0, s)$;
2. no message has been sent: $\forall m,\ \neg W.\mathrm{sent}(m)$.

So every node (eligible or not) has local node $P.\mathrm{dn}(n)$, current term $0$, an accepted state of term $0$ with empty configurations, no votes, $\mathrm{started} = \mathrm{won} = \mathrm{false}$, $\mathrm{lpv} = 0$ and $\mathrm{lpc} = \mathrm{EMPTY}$. The state $s$ may differ from node to node, and its version, metadata version, cluster-manager node, both cluster-UUID flags and payload are unconstrained. The docstring lists only "version, metadata version and payload" as arbitrary; the cluster-manager node and the UUID flags (so a fresh node may have `uuidKnown = true`, even `uuidCommitted = true`) are left free as well.

## Declaration 10: `RestartState`

For cluster states $s$ (the accepted state before the restart) and $s'$ (after), $\mathrm{RestartState}(s, s')$ is the disjunction of

1. (persisted state) $s'.\mathrm{term} = s.\mathrm{term}$, $s'.\mathrm{version} = s.\mathrm{version}$, $s'.\mathrm{lcc} = s.\mathrm{lcc}$, $s'.\mathrm{lac} = s.\mathrm{lac}$, $s'.\mathrm{uuidKnown} = s.\mathrm{uuidKnown}$ and $s'.\mathrm{uuidCommitted} = s.\mathrm{uuidCommitted}$ — the metadata version, the cluster-manager node and the payload of $s'$ are free;
2. (remote-store restore) $s.\mathrm{term} = 0$, $s.\mathrm{lcc} = s.\mathrm{lac} = \mathrm{EMPTY}$, $s.\mathrm{uuidKnown} = \mathrm{false}$, and $s'.\mathrm{term} = 0$, $s'.\mathrm{lcc} = s'.\mathrm{lac} = \mathrm{EMPTY}$ — everything else of $s'$ (version, metadata version, cluster-manager node, UUID flags, payload) is free.

The docstring matches. *Citation check.* GatewayMetaState.java:164-197 builds the restarted node's state from the on-disk metadata (which carries the coordination metadata — term and both configurations — and the cluster UUID with its committed flag) and the persisted version, then rebuilds the rest (`prepareInitialClusterState`); this supports branch 1 (the metadata version is also left free in Lean, which only adds behaviours; the module docstring mentions only the payload and the cluster-manager node as rebuilt). The remote-store restore is GatewayMetaState.java:169-188 (the cited 166-185 is off by a few lines): it is attempted when the node is cluster-manager-eligible, remote cluster state is enabled, the locally loaded cluster UUID is unknown, and the remote store knows a last cluster UUID; the restore starts from `Metadata.EMPTY_METADATA` (GatewayMetaState.java:293-299) and copies back only index metadata, persistent settings, templates, customs and the version (RemoteStoreRestoreService.java:218-267, 279-307), so the coordination metadata stays empty (term 0, empty configurations) while the version is taken from the remote state. Lean's branch 2 has this result but a narrower trigger: Java tests only that the cluster UUID is unknown, whereas Lean also requires the old state to have term 0 and empty configurations. In the Lean model the UUID flags are otherwise unconstrained (bootstrap and client-value states may carry `uuidKnown = false` at term $\geq 1$ or with non-empty configurations), so for such states the Lean restart relation omits a Java restore behaviour; whether such states occur in Java (where bootstrapping generates a UUID) is outside the model.

## Declaration 11: `Step`

$\mathrm{Step}(P, W, W')$ is an inductive relation with nine cases. In each case $W'$ is $W$ with exactly one node's state replaced (via `set`) and possibly one message added (via `send`); no case removes a message. Write $c = W.\mathrm{node}(n)$ for the acting node's state before the step.

1. **`bootstrap`** (node $n$, configuration $X$, cluster state $s$, coordination state $cs'$): if $P.\mathrm{initConfs}(X)$, $\mathrm{initialStateContract}(c, s)$, $s.\mathrm{lcc} = X \wedge s.\mathrm{lac} = X$, and $\mathrm{setInitialState}(c, s)$ succeeds with $cs'$, then $W' = W.\mathrm{set}(n, cs')$. Unfolded: $c$ has accepted term $0$, empty last committed and last accepted configurations, $\mathrm{lpv} = 0$, empty $\mathrm{lpc}$, has not won and holds no votes; $s$ has term $0$, version $c.\mathrm{lav}$, and both configurations equal to the non-empty bootstrap configuration $X$; $cs'$ is $c$ with accepted state $s$ (current term and transient fields unchanged, so $\mathrm{lpc}$ stays empty). The metadata version, cluster-manager node, UUID flags and payload of $s$ are free. Not required: that $n$ be eligible, that $n \in X$, or any quorum of discovered nodes (Java's `setInitialConfiguration`, CO:1101-1161, checks all three and throws otherwise). No message is sent. Several nodes may bootstrap, with different configurations.
2. **`startJoin`** (nodes $n$, $\mathit{src}$, term $t$, $cs'$, join $j$): if $E(\mathit{src})$ and $\mathrm{handleStartJoin}(c, (P.\mathrm{dn}(\mathit{src}), t))$ succeeds with $(cs', j)$, then $W' = (W.\mathrm{set}(n, cs')).\mathrm{send}(\mathrm{join}\ j)$. Unfolded: $t > c.\mathrm{currentTerm}$; $cs'$ has current term $t$, $\mathrm{lpv} = 0$, $\mathrm{lpc} = c.\mathrm{lac}$, $\mathrm{started}$, not won, no votes, same accepted state; $j = (c.\mathrm{localNode},\ P.\mathrm{dn}(\mathit{src}),\ t,\ c.\mathrm{lat},\ \mathrm{vomv}(c.\mathrm{acc}))$. Any node, eligible or not, may do this at any time, for any eligible requester (itself included) and any larger term.
3. **`join`** (node $n$, join $j$, $cs'$, Boolean $b$): if $\mathrm{join}\ j$ has been sent, $j.\mathrm{tgt}.\mathrm{id} = n$, and $\mathrm{handleJoin}(P.\mathrm{strategy}, c, j)$ succeeds with $(cs', b)$, then $W' = W.\mathrm{set}(n, cs')$. ($b$ is unused.)
4. **`clientValue`** (node $n$, cluster state $s$, $cs'$, publish request $p$): if $\mathrm{clientValueContract}(c, s)$ (i.e. $s.\mathrm{lcc} = c.\mathrm{lcc}$) and $\mathrm{handleClientValue}(c, s)$ succeeds with $(cs', p)$, then $W' = (W.\mathrm{set}(n, cs')).\mathrm{send}(\mathrm{PR}(n,\ p.\mathrm{acceptedState},\ c.\mathrm{lat},\ c.\mathrm{lav}))$. Since $p.\mathrm{acceptedState} = s$, the message is $\mathrm{PR}(n, s, c.\mathrm{lat}, c.\mathrm{lav})$: its ghost parent is the publisher's accepted key at that moment. Unfolded conditions: $c.\mathrm{won}$; $c.\mathrm{lpv} = c.\mathrm{lav}$; $s.\mathrm{term} = c.\mathrm{currentTerm}$; $s.\mathrm{version} > c.\mathrm{lpv}$; $s.\mathrm{lac} = c.\mathrm{lac}$ or $c.\mathrm{lcc} = c.\mathrm{lac}$; $c.\mathrm{joinVotes}$ is a quorum of $s.\mathrm{lac}$; $s.\mathrm{lcc} = c.\mathrm{lcc}$. The rest of $s$ is free. $cs'$ is $c$ with $\mathrm{lpv} := s.\mathrm{version}$, $\mathrm{lpc} := s.\mathrm{lac}$, no publish votes.
5. **`publish`** (nodes $n$, $\mathit{src}$, state $s$, $pt$, $pv$, $cs'$, response $r$): if $\mathrm{PR}(\mathit{src}, s, pt, pv)$ has been sent and $\mathrm{handlePublishRequest}(c, s)$ succeeds with $(cs', r)$, then $W' = (W.\mathrm{set}(n, cs')).\mathrm{send}(\mathrm{RESP}(n, \mathit{src}, r))$. Any node $n$ (the publisher itself, an ineligible node, a node never bootstrapped) may handle any sent publish request, any number of times; the ghost parent plays no role; $r = (s.\mathrm{term}, s.\mathrm{version})$ and $cs'$ is $c$ with accepted state $s$.
6. **`respond`** (nodes $n$, $\mathit{src}$, response $r$, $cs'$, optional apply-commit $o$): if $\mathrm{RESP}(\mathit{src}, n, r)$ has been sent (addressed to $n$) and $\mathrm{handlePublishResponse}(c, P.\mathrm{dn}(\mathit{src}), r)$ succeeds with $(cs', o)$, then $W' = W.\mathrm{set}(n, cs')$ if $o$ is none and $W' = (W.\mathrm{set}(n, cs')).\mathrm{send}(\mathrm{AC}(o))$ if $o$ is some apply-commit. The voter added is $P.\mathrm{dn}(\mathit{src})$, so an ineligible responder is never counted; the apply-commit, when produced, is $(c.\mathrm{localNode}, r.\mathrm{term}, r.\mathrm{version})$.
7. **`commit`** (node $n$, apply-commit $a$, $cs'$): if $\mathrm{AC}(a)$ has been sent and $\mathrm{handleCommit}(c, a)$ succeeds with $cs'$, then $W' = W.\mathrm{set}(n, cs')$. Any node may handle any sent apply-commit.
8. **`restart`** (node $n$, state $s'$): if $E(n)$ and $\mathrm{RestartState}(c.\mathrm{acc}, s')$, then $W' = W.\mathrm{set}(n, \mathrm{init}(c.\mathrm{localNode}, c.\mathrm{currentTerm}, s'))$: same local node and current term, accepted state $s'$, transient part reset ($\mathrm{lpc} = s'.\mathrm{lac}$).
9. **`restartAny`** (node $n$, term $t$, state $s'$): if $\neg E(n)$, then $W' = W.\mathrm{set}(n, \mathrm{init}(c.\mathrm{localNode}, t, s'))$, for any $t$ (possibly smaller than before) and any $s'$.

A message's presence in $\mathrm{sent}$ is the only condition on it, and $\mathrm{sent}$ never shrinks, so a sent message can be handled any number of times, or never.

## Declaration 12: `Reachable`

$\mathrm{Reachable}(P, \cdot)$ is the least predicate on clusters that contains every $W$ with $\mathrm{Initial}(P, W)$ and contains $W'$ whenever it contains $W$ and $\mathrm{Step}(P, W, W')$.

## Declaration 13: `Committed`

$\mathrm{Committed}(W, t, v) \iff \exists \sigma,\ W.\mathrm{sent}(\mathrm{AC}(\sigma, t, v))$, the source $\sigma$ ranging over all discovery nodes. The docstring speaks of "a published state (term, version)", but the definition does not require $(t, v)$ to be the key of any publication.

## Declaration 14: `Parent`

$\mathrm{Parent}(W, t, v, t', v') \iff \exists\, \mathit{src}, s,\ W.\mathrm{sent}(\mathrm{PR}(\mathit{src}, s, t, v)) \wedge s.\mathrm{term} = t' \wedge s.\mathrm{version} = v'$: some publication of key $(t', v')$ has ghost parent $(t, v)$. A key may have several parents if several publications share its key (excluded by `Inv` field 20, not by this definition).

## Declaration 15: `Descends`

$\mathrm{Descends}(W, \cdot, \cdot, \cdot, \cdot)$ is the least relation on pairs of keys with (`refl`) $\mathrm{Descends}(W, t, v, t, v)$ for **every** $(t, v)$, and (`step`) $\mathrm{Descends}(W, t, v, t', v') \wedge \mathrm{Parent}(W, t', v', t'', v'') \Rightarrow \mathrm{Descends}(W, t, v, t'', v'')$. Writing $(t, v) \preceq (t'', v'')$ for $\mathrm{Descends}(W, t, v, t'', v'')$ — the *first* key is the ancestor — this holds iff there is a chain $(t, v) = k_0, k_1, \dots, k_m = (t'', v'')$, $m \ge 0$, with $\mathrm{Parent}(k_i, k_{i+1})$ for every $i < m$. The docstring says "descent between published (term, version) pairs", but reflexivity holds for every pair, published or not; a pair that is not the key of a publication has no ancestor but itself. For an arbitrary $W$ the relation may have cycles; acyclicity comes only from `Inv`.

## Declaration 16: `KeyLE`

$\mathrm{KeyLE}(t, v, t', v') \iff t < t' \vee (t = t' \wedge v \le v')$: the lexicographic order on keys.

## Declaration 17: `Below`

$\mathrm{Below}(lt, lv, bt, bv) \iff lt < bt \vee \big(lt = bt \wedge (bt = 0 \vee lv \le bv)\big)$: lexicographic, except that when both terms are $0$ the versions are not compared. `handleJoin` accepts a join $j$ at a node $c$ (as far as guards 3 and 4 go) iff $j.\mathrm{lat} < c.\mathrm{lat} \vee (j.\mathrm{lat} = c.\mathrm{lat} \wedge j.\mathrm{lav} \le \mathrm{vomv}(c.\mathrm{acc}))$; for $c.\mathrm{lat} \ge 1$ this is exactly $\mathrm{Below}(j.\mathrm{lat}, j.\mathrm{lav}, c.\mathrm{lat}, c.\mathrm{lav})$, and for $c.\mathrm{lat} = 0$ `Below` is weaker (it drops the comparison with the metadata version). The docstring says this.

## Declaration 18: `Published`

$\mathrm{Published}(W, t, v) \iff \exists\, \mathit{src}, s, pt, pv,\ W.\mathrm{sent}(\mathrm{PR}(\mathit{src}, s, pt, pv)) \wedge s.\mathrm{term} = t \wedge s.\mathrm{version} = v$. It is not used by any other declaration of this file.

## Declaration 19: `Realizes`

For a key $(t, v)$ and configurations $x$ (in the role of a last committed configuration) and $y$ (last accepted), $\mathrm{Realizes}(P, W, t, v, x, y)$ is the disjunction of

1. $t = 0 \wedge x = y \wedge P.\mathrm{initConfs}(x)$ — the version $v$ is then unconstrained;
2. there is a sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$ with key $(t, v)$, $y = s.\mathrm{lac}$, and either $x = s.\mathrm{lcc}$, or $x = s.\mathrm{lac}$ and $\mathrm{Committed}(W, t, v)$.

The docstring matches; its last sentence (that eligible bootstrapped nodes realize their own key) is a claim made by `Inv` field 11, not by this definition.

## Declarations 20–22: `JoinVoters`, `BaseVoters`, `RespVoters`

For a list $J$ (or $A$) of node ids:

- $\mathrm{JoinVoters}(P, W, L, t, J)$: every $x \in J$ has $E(x)$ and there is a sent $\mathrm{join}\ j$ with $j.\mathrm{src}.\mathrm{id} = x$, $j.\mathrm{tgt}.\mathrm{id} = L$ and $j.\mathrm{term} = t$.
- $\mathrm{BaseVoters}(P, W, L, t, bt, bv, J)$: the same, with in addition $\mathrm{Below}(j.\mathrm{lat}, j.\mathrm{lav}, bt, bv)$ for that join.
- $\mathrm{RespVoters}(P, W, t, v, A)$: every $x \in A$ has $E(x)$ and $\mathrm{RESP}(x, d, (t, v))$ has been sent for some $d$ — the destination is arbitrary.

All three hold vacuously for the empty list and allow repetitions. Docstrings match.

## Declaration 23: `ElectionRecord`

$\mathrm{ElectionRecord}(P, W, L, t, bt, bv, x, y, J) \iff bt < t \wedge \mathrm{Realizes}(P, W, bt, bv, x, y) \wedge \mathrm{BaseVoters}(P, W, L, t, bt, bv, J) \wedge x.\mathrm{hasQuorum}(J) \wedge y.\mathrm{hasQuorum}(J)$. The pair $(bt, bv)$ is called the *base*. Since $J$ is a quorum of $x$, both $x$ and $J$ are non-empty. Nothing requires $L$ to have won, to be eligible (although, under `Inv` field 12, the target of a sent join is eligible) or to have published, nor the base to be published (it may be a term-0 key). The docstring's second sentence (that a node that has just won, and the first publication of a term, carry a record) is a claim about other notions, not part of the definition.

## Declaration 24: `Won`

$\mathrm{Won}(P, W, b, t) \iff E(b) \wedge \big( (W.\mathrm{node}(b).\mathrm{won} \wedge W.\mathrm{node}(b).\mathrm{currentTerm} = t) \vee \exists\, s, pt, pv,\ W.\mathrm{sent}(\mathrm{PR}(b, s, pt, pv)) \wedge s.\mathrm{term} = t \big)$. A node that has published in term $t$ satisfies $\mathrm{Won}(b, t)$ forever, whatever its later state. The docstring matches.

## Declaration 25: `Inv`

$\mathrm{Inv}(P, W)$ is a structure of 30 propositional fields, i.e. their conjunction. Notation: for a node $n$ let $c_n = W.\mathrm{node}(n)$ and write $\mathrm{ln}(n) = c_n.\mathrm{localNode}$, $T(n) = c_n.\mathrm{currentTerm}$, $\mathrm{lat}(n), \mathrm{lav}(n), \mathrm{lcc}(n), \mathrm{lac}(n)$ for $c_n.\mathrm{lat}, c_n.\mathrm{lav}, c_n.\mathrm{lcc}, c_n.\mathrm{lac}$, $\mathrm{won}(n)$, $\mathrm{started}(n)$, $\mathrm{lpv}(n)$, $\mathrm{lpc}(n)$, and $\mathrm{JV}(n)$, $\mathrm{PV}(n)$ for the node-id lists of $c_n$'s join and publish votes; "sent" means in $W.\mathrm{sent}$; node variables range over all of $\mathbb{N}$.

*Every node $n$:*

1. `localNode_eq`: $\mathrm{ln}(n) = P.\mathrm{dn}(n)$.
2. `idle_of_not_won` (N4): $\neg\mathrm{won}(n) \Rightarrow \mathrm{lpv}(n) = 0 \wedge \mathrm{PV}(n) = [\,]$. The docstring's "has published nothing in its term" is stronger than the term, which constrains only the local variables: a node that published in its term and then restarted has $\mathrm{lpv} = 0$ although its publication is in $\mathrm{sent}$.
3. `won_started` (N2): $\mathrm{won}(n) \Rightarrow \mathrm{started}(n)$.
4. `votes_started` (N6): $\mathrm{JV}(n) \neq [\,] \Rightarrow \mathrm{started}(n)$.
5. `started_term_pos` (N10): $\mathrm{started}(n) \Rightarrow T(n) \ge 1$.
6. `won_quorum` (N3): $\mathrm{won}(n) \Rightarrow \mathrm{JV}(n)$ is a quorum of $\mathrm{lcc}(n)$ and a quorum of $\mathrm{lac}(n)$.
7. `not_won_no_quorum` (N3r): $\neg\mathrm{won}(n) \Rightarrow \neg\big(\mathrm{JV}(n)$ is a quorum of $\mathrm{lcc}(n)$ and of $\mathrm{lac}(n)\big)$. The docstring calls this "the reverse half of `invariant()`". Java's `invariant()` asserts `electionWon == isElectionQuorum(joinVotes)`, whose reverse half also includes the strategy's additional constraint; the field omits it and is therefore stronger, coinciding with Java's reverse half only when the strategy's constraint is always true (for instance the default strategy). `Inv` never mentions $P.\mathrm{strategy}$.
8. `joinVotes_sent` (N8): for every $m \in \mathrm{JV}(n)$: $E(m)$, and some sent $\mathrm{join}\ j$ has $j.\mathrm{src}.\mathrm{id} = m$, $j.\mathrm{tgt}.\mathrm{id} = n$, $j.\mathrm{term} = T(n)$ and $\mathrm{Below}(j.\mathrm{lat}, j.\mathrm{lav}, \mathrm{lat}(n), \mathrm{lav}(n))$.
9. `publishVotes_sent` (N9): for every $m \in \mathrm{PV}(n)$: $E(m)$ and $\mathrm{RESP}(m, n, (T(n), \mathrm{lpv}(n)))$ has been sent.

*Every eligible node $n$:*

10. `term_le` (N1): $E(n) \Rightarrow \mathrm{lat}(n) \le T(n)$.
11. `accepted_realizes` (N7): $E(n) \Rightarrow \big(\mathrm{lat}(n) = 0 \wedge \mathrm{lcc}(n) = \mathrm{EMPTY} \wedge \mathrm{lac}(n) = \mathrm{EMPTY}\big) \vee \mathrm{Realizes}(\mathrm{lat}(n), \mathrm{lav}(n), \mathrm{lcc}(n), \mathrm{lac}(n))$.

*Joins and publish responses:*

12. `join_wf`: every sent $\mathrm{join}\ j$ has $j.\mathrm{src} = P.\mathrm{dn}(j.\mathrm{src}.\mathrm{id})$ and $E(j.\mathrm{tgt}.\mathrm{id})$.
13. `join_term_le` (J1): every sent $\mathrm{join}\ j$ with $E(j.\mathrm{src}.\mathrm{id})$ has $j.\mathrm{term} \le T(j.\mathrm{src}.\mathrm{id})$.
14. `join_unique` (J2): any two sent joins $j, j'$ with $E(j.\mathrm{src}.\mathrm{id})$, $j.\mathrm{src}.\mathrm{id} = j'.\mathrm{src}.\mathrm{id}$ and $j.\mathrm{term} = j'.\mathrm{term}$ are equal (all five fields, in particular the same target).
15. `join_after_response` (J3): for every sent $\mathrm{join}\ j$ and sent $\mathrm{RESP}(a, d, (t, v))$ with $j.\mathrm{src}.\mathrm{id} = a$, $E(a)$ and $t < j.\mathrm{term}$: $\mathrm{KeyLE}(t, v, j.\mathrm{lat}, j.\mathrm{lav})$.
16. `response_le` (R1): for every sent $\mathrm{RESP}(a, d, (t, v))$ with $E(a)$: $t \le T(a)$ and $\mathrm{KeyLE}(t, v, \mathrm{lat}(a), \mathrm{lav}(a))$.
17. `response_published` (R2): for every sent $\mathrm{RESP}(a, d, (t, v))$ (no eligibility condition) there is a sent $\mathrm{PR}(d, s, pt, pv)$ **from $d$** with key $(t, v)$.

*Publications* (for every sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$):

18. `pub_wf` (P1): $E(\mathit{src})$, $s.\mathrm{term} \ge 1$, $pt \le s.\mathrm{term}$, $pv < s.\mathrm{version}$, and $pt = 0 \Rightarrow P.\mathrm{initConfs}(s.\mathrm{lcc})$.
19. `pub_parent` (P1, P5): if $pt \ge 1$, there is a sent $\mathrm{PR}(\mathit{src}', s', pt', pv')$ with key $(pt, pv)$ such that (a) $s.\mathrm{lcc} = s'.\mathrm{lcc}$, or ($s.\mathrm{lcc} = s'.\mathrm{lac}$ and $\mathrm{Committed}(pt, pv)$); and (b) $s.\mathrm{lac} \neq s'.\mathrm{lac} \Rightarrow s.\mathrm{lcc} = s'.\mathrm{lac}$.
20. `pub_unique` (P2): any two sent publications with the same key are the same message: same source, same cluster state (all nine fields), same parent.
21. `pub_rooted`: $\exists v_0 \in \mathbb{Z},\ (0, v_0) \preceq (s.\mathrm{term}, s.\mathrm{version})$. (The docstring's gloss "the chain of its ancestors is finite" is an interpretation; the term asserts a finite parent chain from some term-0 key.)
22. `pub_same_term` (P4): for every other sent $\mathrm{PR}(\mathit{src}', s', pt', pv')$ with $s'.\mathrm{term} = s.\mathrm{term}$: $(s.\mathrm{term}, s.\mathrm{version}) \preceq (s'.\mathrm{term}, s'.\mathrm{version})$ or the converse.
23. `pub_voters` (P6): there is a list $J$ with $\mathrm{JoinVoters}(\mathit{src}, s.\mathrm{term}, J)$ that is a quorum of $s.\mathrm{lcc}$ and of $s.\mathrm{lac}$.
24. `pub_election` (P7): if $pt < s.\mathrm{term}$, there are a configuration $y$ and a list $J$ with $\mathrm{ElectionRecord}(\mathit{src}, s.\mathrm{term}, pt, pv, s.\mathrm{lcc}, y, J)$.

*Commits:*

25. `commit_quorum` (C1, D1): for every sent $\mathrm{AC}(\sigma, t, v)$ there are a sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$ with key $(t, v)$ and a list $A$ with $\mathrm{RespVoters}(t, v, A)$, $A$ a quorum of $s.\mathrm{lac}$, and either $A$ a quorum of $s.\mathrm{lcc}$, or ($\mathrm{Committed}(pt, pv)$ and some sent $\mathrm{PR}(\mathit{src}', s', pt', pv')$ with key $(pt, pv)$ has $s'.\mathrm{lac} = s.\mathrm{lac}$).

*Leaders:*

26. `won_unique` (L1): $\mathrm{Won}(a, t) \wedge \mathrm{Won}(b, t) \Rightarrow a = b$.
27. `pub_source_term` (L2): for every sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$: $s.\mathrm{term} < T(\mathit{src})$, or $s.\mathrm{term} = T(\mathit{src})$ and ($\mathrm{won}(\mathit{src})$ or $\neg\mathrm{started}(\mathit{src})$).
28. `leader_pubs` (L3): if $\mathrm{won}(n)$, then every sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$ with $s.\mathrm{term} = T(n)$ — from **any** source — has $s.\mathrm{version} \le \mathrm{lpv}(n)$, $(s.\mathrm{term}, s.\mathrm{version}) \preceq (T(n), \mathrm{lpv}(n))$, and $\mathrm{JV}(n)$ a quorum of $s.\mathrm{lcc}$ and of $s.\mathrm{lac}$. (The docstring says "an elected node's publications of its term"; the term covers all publications of that term.)
29. `leader_inflight` (L4): if $\mathrm{won}(n)$ and $\mathrm{lpv}(n) \neq \mathrm{lav}(n)$, there is a state $s$ with $\mathrm{PR}(n, s, \mathrm{lat}(n), \mathrm{lav}(n))$ sent, $s.\mathrm{term} = T(n)$, $s.\mathrm{version} = \mathrm{lpv}(n)$, $\mathrm{lpc}(n) = s.\mathrm{lac}$, and either $\mathrm{lcc}(n) = s.\mathrm{lcc}$, or ($\mathrm{lcc}(n) = s.\mathrm{lac}$, $\mathrm{Committed}(\mathrm{lat}(n), \mathrm{lav}(n))$ and $\mathrm{lac}(n) = s.\mathrm{lac}$).
30. `leader_settled` (L5): if $\mathrm{won}(n)$ and $\mathrm{lpv}(n) = \mathrm{lav}(n)$: either ($\mathrm{lat}(n) = T(n)$ and $\mathrm{lpc}(n) = \mathrm{lac}(n)$), or ($\mathrm{lat}(n) < T(n)$ and no sent publication has term $T(n)$).

Docstrings of the remaining fields match their terms. Labels: `localNode_eq`, `join_wf` and `pub_rooted` carry none; "R1"/"R2" name both fields 16/17 and the two clauses (a)/(b) of field 19 in its docstring; "P1" names fields 18 and 19. The structure docstring's split — persisted facts for eligible nodes only, transient facts for every node — holds with the nuance that some every-node fields (5–8) mention persisted components, under a transient premise.

*Satisfiability.* Every `Initial` cluster satisfies all 30 fields: fields 1, 2, 10 and 11 by direct check, field 7 because $\mathrm{EMPTY}$ has no quorum, the others vacuously (no message sent, no node won, started or holding votes). So `Inv` is not contradictory. Its preservation by `Step` is not part of this file.

## The module and section docstrings

- The network description ("a message, once sent, stays available forever and may be handled any number of times, by any node it is addressed to, or never") matches `Step`: joins are handled only by their target id, responses only by their destination, publish requests and apply-commits by any node.
- "Each step is a successful call of one `CoordinationState` method, its output, if any, being sent" matches; `restart`/`restartAny` call the constructor. "The steps cover every call the `Coordinator` makes … the `Coordinator`'s own guards only reject more" was checked only for the one cited method, CO:1101-1161 (`Coordinator.setInitialConfiguration`), whose extra guards (eligible local node, local node in the configuration, quorum of discovered nodes) are indeed absent from the Lean step; the bullet attributes it to `ClusterBootstrapService`, which calls it.
- "nodes may bootstrap with different configurations (see `BootstrapConfig`)": the step uses $P.\mathrm{initConfs}$; `BootstrapConfig` is not connected to it in this file.
- The `restart` bullet matches branch 1 and `restartAny`; for the remote-store branch see Declaration 10 (narrower trigger than Java's). GatewayMetaState.java:164-197 and the use of `LucenePersistedState` for cluster-manager nodes (line 200) versus `AsyncLucenePersistedState` (lines 202-206) or `InMemoryPersistedState` (line 255) for others match the description.
- The assumption citing GatewayMetaState.java:232-255 matches: a node started with neither the cluster-manager nor the data role writes term 0 and an empty state to disk.
- `CoordinationStateTestCluster` (test/framework, `invariant()` at lines 331-370) checks one cluster-manager per term and one state per (term, version) over all publish requests, after random runs in which messages are never removed, start-join terms are occasionally random, elected nodes occasionally publish random terms, versions and configurations, and nodes reboot (also toggling the cluster-manager role, and resetting ineligible nodes' state). The docstring's "the first two safety properties" refers to a list not present in this file.
- Section docstring: "Publications thus form a forest: following parents, versions strictly decrease until a term-0 key" is a consequence of `Inv` (fields 18, 20, 21), not of the definitions, which allow arbitrary $W.\mathrm{sent}$.
