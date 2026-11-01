SRC = ("OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: CoordinationState (the per-node handlers as transcribed by the "
       "OpenSearchCoordination mission; handleCommit lines 523-573, isPublishQuorum 156-158, invariant 601-611): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; "
       "Coordinator (the calls into CoordinationState: handleApplyCommit lines 419-452, handlePublishRequest 454-526, "
       "startElection 583-602, abdicateTo 604-620, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, "
       "setInitialConfiguration 1101-1161, handleJoin 1267-1299, publish 1350 with the handleClientValue call at 1404, "
       "CoordinatorPublication.handlePublishResponse 1871-1876): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; "
       "ClusterBootstrapService (requirements 146-157, onFoundPeersUpdated 176-215, startBootstrap 259-273, checkRequirements 306-335): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ClusterBootstrapService.java#L146-L335; "
       "GatewayMetaState.start (persisted state loaded and rebuilt 141-231, remote restore 169-188, synchronous and asynchronous persistence 199-207, "
       "nodes without the cluster-manager and data roles 232-255): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/gateway/GatewayMetaState.java#L126-L257; "
       "PersistedStateRegistry.addPersistedState (lines 38-41): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/PersistedStateRegistry.java#L38-L41; "
       "ElectionStrategy (DEFAULT_INSTANCE lines 46-59): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionStrategy.java#L44-L110; "
       "the randomized safety test CoordinationStateTestCluster (reboot 156-193, runRandomly 279-329, invariant 331-370): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/test/framework/src/main/java/org/opensearch/cluster/coordination/CoordinationStateTestCluster.java "
       "and CoordinationStateTests.testSafety (lines 917-924): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/test/java/org/opensearch/cluster/coordination/CoordinationStateTests.java#L917-L924; "
       "for comparison, Elastic's TLA+ model ZenWithTerms (HandleCommit 241-250, CommittedValuesDescendantsFromInitialValue 338-347, "
       "CommitHasQuorumVsPreviousCommittedConfiguration 349-358): "
       "https://github.com/elastic/elasticsearch-formal-models/blob/ca30663506a7e18de9d23fabbc70a369903d7c98/ZenWithTerms/tla/ZenWithTerms.tla")
TAGS = ["opensearch", "elasticsearch", "consensus", "cluster-coordination", "zen2", "raft", "paxos", "safety",
        "inductive-invariant", "leader-election", "reconfiguration", "message-passing", "crash-recovery",
        "formal-verification"]

DEFINITION = {
    "definition_name": "OpenSearchSafety",
    "definition_title": "OpenSearch coordination as a message-passing system: every node runs CoordinationState, messages may be lost, duplicated or reordered, nodes restart; the safety vocabulary and the inductive invariant",
    "natural_language_statement": r"""A model of an OpenSearch cluster at revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19` in which every node runs the `CoordinationState` of the `OpenSearchCoordination` mission (its `NodeId`, `DiscoveryNode`, `VotingConfiguration`, `ClusterState`, message types, `ElectionStrategy`, `CoordinationState`, handlers and contracts are used as they are), the notions in which the safety theorems are stated, and the inductive invariant `Inv` from which they are proved. `CO` is `Coordinator.java`, `CBS` is `ClusterBootstrapService.java`.

**Messages.** **`Message V`** — `join j`, a `Join`; `publishRequest source state parentTerm parentVersion`, a `PublishRequest` of `state` from `source`, together with ghost data that the real message does not carry: the term and version of the state the publisher had accepted when it published, the publication's *parent*; `publishResponse source dest resp`, a `PublishResponse` from `source` to `dest`; `applyCommit c`, an `ApplyCommitRequest`.

**Parameters.** **`Params`** — `eligible n`, whether node `n` has the cluster-manager role (`DiscoveryNode.isClusterManagerNode()`, fixed); `initConfs`, the configurations a node may bootstrap with (a predicate on configurations); `strategy`, the election strategy of every node. **`P.dn n`** — the `DiscoveryNode` `⟨n, P.eligible n⟩`. **`P.InitCompatible`** — for all configurations `X`, `Y` with `P.initConfs X` and `P.initConfs Y` and all lists `q₁`, `q₂` of eligible node ids with `X.hasQuorum q₁` and `Y.hasQuorum q₂`, some node id is in both lists. **`BootstrapConfig k resolve placeholder matched X`** — `X` has the form of a configuration that `ClusterBootstrapService` bootstraps with (CBS:176-215, 259-273, 306-335): the `k` bootstrap requirements (`cluster.initial_cluster_manager_nodes`) are numbered `0 … k-1`; the members of `X` are exactly, for `i < k`, `resolve i` if `matched i` (the node has discovered the node requirement `i` names) and the placeholder id `placeholder i` otherwise (`"{bootstrap-placeholder}-" + requirement`); and more than half of the `k` requirements are matched. The predicate does not require `resolve` or `placeholder` to be injective or their values to be distinct (`bootstrap_compatible` assumes this; in Java the requirements have no duplicates and `checkRequirements` matches each requirement and each discovered node at most once, CBS:150-155, 306-335), nor the bootstrapping node to be eligible and matched (Java requires both, CBS:179, 202-209); no other definition refers to it (the `bootstrap` step uses `P.initConfs`).

**Clusters.** **`Cluster V`** — `node : NodeId → CoordinationState V`, the state of every node, and `sent : Message V → Prop`, the messages sent so far. **`W.set n cs`** replaces node `n`'s state by `cs`; **`W.send m`** adds `m` to the sent messages. **`Initial P W`** — every node `n` is `CoordinationState.init (P.dn n) 0 s` for some cluster state `s` of term 0 whose last committed and last accepted configurations are empty (its other fields, version and metadata version included, are arbitrary), and no message has been sent. **`RestartState s s'`** — the accepted state `s'` a restarting cluster-manager-eligible node comes back with, given the accepted state `s` it had: `s'` has the term, the version, the two configurations and the two cluster-UUID flags of `s` (its metadata version, cluster-manager node and payload may differ: Java rebuilds the cluster-manager node and the parts of the state outside the persisted metadata, and leaving the persisted metadata, metadata version included, free only adds behaviours); or `s` has term 0, empty configurations and an unknown cluster UUID, and `s'` has term 0 and empty configurations (a node that never joined a cluster, restoring a state from the remote store).

**Steps.** **`Step P W W'`** — one successful handler call at a node `n`, its output, if any, being added to the sent messages:
- `bootstrap`: `(W.node n).setInitialState s = .ok cs'` for a state `s` whose two configurations are some `X` with `P.initConfs X`, with `initialStateContract` (the method's asserted preconditions); `W' = W.set n cs'`;
- `startJoin`: `handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)` for any eligible `src` and any term `t`; `W' = (W.set n cs').send (.join j)`;
- `join`: `handleJoin P.strategy j = .ok (cs', b)` for a sent join `j` with `j.targetNode.id = n`; `W' = W.set n cs'`;
- `clientValue`: `handleClientValue s = .ok (cs', p)` with `clientValueContract` (the asserted precondition: `s` carries `n`'s last committed configuration); sends `publishRequest n p.acceptedState lt lv`, where `(lt, lv)` are `n`'s last accepted term and version before the call;
- `publish`: `handlePublishRequest ⟨s⟩ = .ok (cs', r)` for a sent `publishRequest src s pt pv`; sends `publishResponse n src r`;
- `respond`: `handlePublishResponse (P.dn src) r = .ok (cs', o)` for a sent `publishResponse src n r`; sends `applyCommit c` if `o = some c`;
- `commit`: `handleCommit c = .ok cs'` for a sent `applyCommit c`;
- `restart`: for an eligible `n`, the state becomes `CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'` for a state `s'` with `RestartState (W.node n).lastAcceptedState s'`;
- `restartAny`: for a node `n` that is not eligible, the state becomes `CoordinationState.init (W.node n).localNode t s'` for any term `t` and any state `s'`.

**`Reachable P W`** — `W` is initial, or is reached from a reachable cluster by a step.

**Safety vocabulary.** A publication is named by its *key*, its (term, version). **`Committed W t v`** — some `applyCommit ⟨src, t, v⟩` has been sent. **`Parent W t v t' v'`** — some `publishRequest src s t v` with `s.term = t'` and `s.version = v'` has been sent. **`Descends W t v t' v'`** — the reflexive-transitive closure of `Parent`: `(t', v')` descends from `(t, v)`.

**Proof-side notions** (used by `Inv`, the lemmas and their proofs only; `Published` appears only in the proofs). **`KeyLE t v t' v'`** — `t < t' ∨ (t = t' ∧ v ≤ v')`. **`Below lt lv bt bv`** — `lt < bt ∨ (lt = bt ∧ (bt = 0 ∨ lv ≤ bv))`: `handleJoin`'s freshness comparison, ignoring the version at term 0, where joins carry metadata versions. **`Published W t v`** — some publication of term `t` and version `v` has been sent. **`Realizes P W t v x y`** — the pair (last committed, last accepted) `(x, y)` realizes the key `(t, v)`: `t = 0`, `x = y` and `P.initConfs x` (a bootstrap state); or some sent publication of term `t` and version `v` has last accepted configuration `y`, and last committed configuration `x`, or last accepted configuration `x` with `(t, v)` committed. **`JoinVoters P W L t J`** — every member of `J` is eligible and sent node `L` a join of term `t`. **`BaseVoters P W L t bt bv J`** — every member of `J` is eligible and sent `L` a join of term `t` whose last accepted term and version are `Below bt bv`. **`RespVoters P W t v A`** — every member of `A` is eligible and sent a `PublishResponse` for `(t, v)` to some node. **`ElectionRecord P W L t bt bv x y J`** — `bt < t`, `Realizes P W bt bv x y`, `BaseVoters P W L t bt bv J`, `x.hasQuorum J` and `y.hasQuorum J`: an election of `L` in term `t` over the base `(bt, bv)`. **`Won P W b t`** — `b` is eligible, and either `(W.node b).electionWon = true` with current term `t`, or `b` has sent a publication of term `t`.

**`Inv P W`** — the inductive invariant, 30 facts (field names in parentheses).
- Every node `n`: its local node is `P.dn n` (`localNode_eq`); if it has not won, its last published version is 0 and its publish votes are empty (`idle_of_not_won`); if it has won, and if it holds join votes, it has handled a start-join since its last restart (`won_started`, `votes_started`); if it has handled one, its current term is at least 1 (`started_term_pos`); its join votes are a quorum of both its last committed and its last accepted configuration if it has won (`won_quorum`) and not if it has not (`not_won_no_quorum`); every join vote it holds is of an eligible node that sent it a join for its current term with a last accepted term and version `Below` its own (`joinVotes_sent`); every publish vote it holds is of an eligible node that sent it a `PublishResponse` for its current term and last published version (`publishVotes_sent`).
- Every eligible node: its last accepted term is at most its current term (`term_le`); its accepted state has term 0 and empty configurations, or its two configurations realize its last accepted term and version (`accepted_realizes`).
- Joins and responses: every join is from the `DiscoveryNode` of its source and addressed to an eligible node (`join_wf`); the joins of an eligible node have terms at most its current term (`join_term_le`), at most one per term (`join_unique`), and a join of an eligible node for a term later than one of its publish responses carries a last accepted (term, version) at least the response's (`join_after_response`); the publish responses of an eligible node have terms at most its current term and keys at most its last accepted key (`response_le`); every publish response answers a publication of its key sent by the node it is addressed to (`response_published`).
- Publications: every publication is sent by an eligible node, has term ≥ 1, a parent of term at most its term and of smaller version, and, if the parent has term 0, a bootstrap configuration as last committed configuration (`pub_wf`); a parent of term ≥ 1 is the key of a sent publication, the last committed configuration is that publication's last committed one, or its last accepted one if the parent is committed, and the last accepted configuration differs from that publication's only if the last committed configuration is that publication's last accepted one (`pub_parent`); two publications with the same key are the same message (`pub_unique`); every publication descends from a key of term 0 (`pub_rooted`); two publications of the same term are related by descent (`pub_same_term`); the eligible nodes that sent the publisher a join for the publication's term include a quorum of both its configurations (`pub_voters`); a publication whose parent is of an older term carries an election record of its publisher for its term, over the parent, with its last committed configuration as `x` (`pub_election`).
- Commits: every commit is of a sent publication whose publish responses from eligible nodes include a quorum `A` of its last accepted configuration such that `A` is also a quorum of its last committed configuration, or the publication's parent is committed and is a sent publication with the same last accepted configuration (`commit_quorum`).
- Leaders: for each term `t`, at most one node `b` has `Won P W b t` (`won_unique`); a node that published in a term is past that term, or still in it and either elected or without a start-join handled since its last restart (`pub_source_term`); every publication of an elected node's current term has a version at most the node's last published version, descends to (current term, last published version), and has both configurations with a quorum in the node's join votes (`leader_pubs`); an elected node whose last published version differs from its last accepted version sent a publication of key (current term, last published version) with its accepted key as parent, its last published configuration is that publication's last accepted configuration, and its last committed configuration is that publication's last committed one, or that publication's last accepted one with its accepted key committed and its last accepted configuration equal to that publication's (`leader_inflight`); an elected node whose last published version equals its last accepted version has its last accepted term equal to its current term and its last published configuration equal to its last accepted one, or an older last accepted term while no publication of its current term has been sent (`leader_settled`).

**Formalization Note.** Messages are never removed: a step may handle any sent message any number of times, in any order, or never, which models loss, duplication, delay and reordering. A join is handled only by its target and a publish response only by its addressee; publish requests and commits may be handled by any node. Start-join requests are not messages: any node may handle a request from any eligible node for any term at any time, which covers the `Coordinator`'s elections, abdication and `ensureTermAtLeast` (CO:583-657) and over-approximates them; the `Coordinator`'s other guards only reject more calls. The asserted preconditions of `setInitialState` and `handleClientValue` are imposed at the `bootstrap` and `clientValue` steps. The ghost parent of a publication is not read by any handler. A cluster-manager-eligible node persists its current term and accepted state synchronously; a restart keeps its current term and either keeps its accepted state except for the metadata version, the cluster-manager node and the payload, which it leaves free, or, if the node never joined a cluster (term 0, empty configurations, unknown cluster UUID), replaces it by a term-0 state with empty configurations, as restored from the remote store (`RestartState`); a node that is not cluster-manager-eligible may come back with any term and state. Outside the model (assumptions): a node's cluster-manager role never changes; persisted state is never rolled back; the offline `opensearch-node` tools are not used; bootstrap requirements name the same node at every node; every node uses the same election strategy; a publication delivered through the remote cluster-state store reconstructs exactly the published state. The per-node abstractions of `OpenSearchCoordination` apply (terms are naturals, versions integers without overflow, the remote persisted state omitted). The safety theorems assume `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`. The file imports only the `OpenSearchCoordination` definitions (Lean core).""",
}

THEOREMS = {
"OpenSearchSafety.descends_trans": dict(
    title="Descent between publications is transitive",
    nl=r"""For every payload type `V`, cluster `W` and keys `(t₁, v₁)`, `(t₂, v₂)`, `(t₃, v₃)`: if `Descends W t₁ v₁ t₂ v₂` and `Descends W t₂ v₂ t₃ v₃` then `Descends W t₁ v₁ t₃ v₃`. Nothing is assumed about `W`: `Descends` is the reflexive-transitive closure of `Parent`, where `Parent W t v t' v'` says that a publication of key `(t', v')` was sent with ghost parent `(t, v)`.""",
    ms=None),
"OpenSearchSafety.inv_descends_key": dict(
    title="Along a descent the term never decreases and the version strictly increases",
    nl=r"""For all cluster parameters `P`, every cluster `W` with `Inv P W` (the inductive invariant) and keys `(t, v)`, `(t', v')` with `Descends W t v t' v'`: `t = t' ∧ v = v'`, or `t ≤ t' ∧ v < v'`. Each link of a descent is a sent publication whose ghost parent has a term at most its term and a smaller version (`pub_wf`). In particular a descent between distinct keys strictly increases the version, so descent is antisymmetric.""",
    ms=None),
"OpenSearchSafety.inv_descends_parent": dict(
    title="A proper ancestor of a publication is an ancestor of its parent",
    nl=r"""For all `P`, every cluster `W` with `Inv P W`, every sent publication `W.sent (.publishRequest src s pt pv)` and every key `(t, v)` with `Descends W t v s.term s.version` and `¬ (t = s.term ∧ v = s.version)`: `Descends W t v pt pv`. Two publications with the same key are the same message (`pub_unique`), so a key has a single parent, the ghost parent `(pt, pv)` of its publication, and a non-trivial descent into the key passes through it.""",
    ms=None),
"OpenSearchSafety.inv_descends_linear": dict(
    title="The ancestors of a key form a chain",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and keys `(t₁, v₁)`, `(t₂, v₂)`, `(t, v)` with `Descends W t₁ v₁ t v` and `Descends W t₂ v₂ t v`: `Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁`. Since every key has at most one parent, the published states form a forest and two ancestors of one key are comparable.""",
    ms=None),
"OpenSearchSafety.inv_reign_first": dict(
    title="Every publication descends from a first publication of its term",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every sent publication `W.sent (.publishRequest src s pt pv)`, there is a sent publication `W.sent (.publishRequest src' s' pt' pv')` with `s'.term = s.term`, `pt' < s'.term` and `Descends W s'.term s'.version s.term s.version`. The first publication of a term is the one whose parent is of an older term: the state its publisher had accepted when it won the election.""",
    ms=None),
"OpenSearchSafety.inv_committed_published": dict(
    title="A committed key is the key of a publication, of term at least 1",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every key with `Committed W t v` (some `ApplyCommitRequest` for term `t` and version `v` has been sent): `1 ≤ t`, and some publication `W.sent (.publishRequest src s pt pv)` with `s.term = t` and `s.version = v` has been sent.""",
    ms=None),
"OpenSearchSafety.inv_eligible_of_won": dict(
    title="Only cluster-manager-eligible nodes win elections",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every node `n` with `(W.node n).electionWon = true`: `P.eligible n = true`. A node that has won holds join votes forming a quorum, hence at least one; every vote it holds comes from a sent join addressed to it (`joinVotes_sent`), and joins are addressed only to eligible nodes (`join_wf`).""",
    ms=None),
"OpenSearchSafety.inv_won_of_electionWon": dict(
    title="A node that has won its election has won its current term",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every node `n` with `(W.node n).electionWon = true`: `Won P W n (W.node n).currentTerm`, that is, `n` is cluster-manager-eligible and has currently won the election of its current term.""",
    ms=None),
"OpenSearchSafety.inv_deepest_committed": dict(
    title="Every key has a deepest committed ancestor, or none",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every key `(t, v)`, one of the following holds:
- there is a committed key `(dt, dv)` with `Descends W dt dv t v` such that every committed `(et, ev)` with `Descends W et ev t v` satisfies `Descends W et ev dt dv` (the deepest committed ancestor-or-self of `(t, v)`);
- no committed key `(et, ev)` satisfies `Descends W et ev t v`.""",
    ms=None),
"OpenSearchSafety.inv_first_committed": dict(
    title="Every committed key has a first committed ancestor",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every committed key `(t, v)` (`Committed W t v`), there is a committed key `(et, ev)` with `Descends W et ev t v` such that every committed `(ft, fv)` with `Descends W ft fv et ev` equals `(et, ev)`: the first committed key on the branch of `(t, v)`, which has no committed proper ancestor.""",
    ms=None),
"OpenSearchSafety.inv_first_committed_after": dict(
    title="Between a key and a committed descendant there is a committed key closest to the first",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and keys `(dt, dv)`, `(ct, cv)` with `Descends W dt dv ct cv`, `¬ (dt = ct ∧ dv = cv)` and `Committed W ct cv`, there is a committed key `(et, ev)` with `Descends W dt dv et ev`, `¬ (dt = et ∧ dv = ev)` and `Descends W et ev ct cv`, such that every committed `(ft, fv)` with `Descends W dt dv ft fv` and `Descends W ft fv et ev` is `(dt, dv)` or `(et, ev)`. Strictly after `d` on the way to `c`, `(et, ev)` is the first committed key.""",
    ms=None),
"OpenSearchSafety.inv_lineage": dict(
    title="Path summary: across uncommitted publications, an accepted configuration stays in force",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and two sent publications `W.sent (.publishRequest srcD sD ptD pvD)` and `W.sent (.publishRequest srcE sE ptE pvE)` such that
- `Descends W sD.term sD.version sE.term sE.version` and `¬ (sD.term = sE.term ∧ sD.version = sE.version)`, and
- no committed key lies strictly between them: every committed `(ft, fv)` with `Descends W sD.term sD.version ft fv` and `Descends W ft fv sE.term sE.version` is `(sD.term, sD.version)` or `(sE.term, sE.version)`,

we have `sE.lastCommittedConfiguration = sD.lastAcceptedConfiguration ∨ sE.lastAcceptedConfiguration = sD.lastAcceptedConfiguration`.

The last committed configuration is copied from the parent unless the parent is committed, and the last accepted configuration changes only when the last committed configuration is the parent's last accepted one (`pub_parent`, the transcription of `handleClientValue`'s reconfiguration guard and of the asserted copying of the committed configuration). Hence at most one reconfiguration is in flight between commits: the configuration accepted at `D` is one of the two configurations of every publication `E` that descends from `D`, with a different key and no committed key strictly between them (`D` and `E` themselves may be committed).""",
    ms=("Path summary", "Induction on the descent from D to E: at each link, the parent is D (use the two reconfiguration rules) or an uncommitted publication strictly between them (its last committed configuration is copied, and the induction hypothesis applies).")),
"OpenSearchSafety.inv_root_lcc": dict(
    title="A publication without committed proper ancestor carries a bootstrap configuration as last committed configuration",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every sent publication `W.sent (.publishRequest src s pt pv)` such that every committed `(ft, fv)` with `Descends W ft fv s.term s.version` equals `(s.term, s.version)` (the publication has no committed proper ancestor): `P.initConfs s.lastCommittedConfiguration`.""",
    ms=None),
"OpenSearchSafety.inv_commit_quorum_after": dict(
    title="The responders to the next commit above a publication include a quorum of its accepted configuration",
    nl=r"""For all `P`, every cluster `W` with `Inv P W`, every sent publication `W.sent (.publishRequest srcD sD ptD pvD)` and every committed key `(ct, cv)` (`Committed W ct cv`) with `Descends W sD.term sD.version ct cv`, `¬ (sD.term = ct ∧ sD.version = cv)`, and no committed key strictly between (every committed `(ft, fv)` with `Descends W sD.term sD.version ft fv` and `Descends W ft fv ct cv` is `(sD.term, sD.version)` or `(ct, cv)`): there is a list `A` with `RespVoters P W ct cv A` (eligible nodes that each sent a `PublishResponse` for `(ct, cv)`) and `sD.lastAcceptedConfiguration.hasQuorum A = true`.""",
    ms=None),
"OpenSearchSafety.inv_commit_quorum_first": dict(
    title="The responders to a first committed key include a quorum of a bootstrap configuration",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every committed key `(ct, cv)` such that every committed `(ft, fv)` with `Descends W ft fv ct cv` equals `(ct, cv)` (no committed proper ancestor): there are a configuration `X` with `P.initConfs X` and a list `A` with `RespVoters P W ct cv A` and `X.hasQuorum A = true`.""",
    ms=None),
"OpenSearchSafety.inv_pivot": dict(
    title="The pivot of a realized base: its deepest committed ancestor carries one of its two configurations",
    nl=r"""For all `P`, every cluster `W` with `Inv P W`, every key `(bt, bv)` and configurations `x`, `y` with `Realizes P W bt bv x y`, one of the following holds:
- there is a sent publication `W.sent (.publishRequest src s pt pv)` with `Committed W s.term s.version` and `Descends W s.term s.version bt bv`, such that every committed `(et, ev)` with `Descends W et ev bt bv` satisfies `Descends W et ev s.term s.version` (it is the deepest committed ancestor-or-self of the base), and `x = s.lastAcceptedConfiguration ∨ y = s.lastAcceptedConfiguration`;
- no committed `(et, ev)` satisfies `Descends W et ev bt bv`, and `P.initConfs x`.

Any pair of configurations a node or a publication can hold for the base thus contains the last configuration committed on its branch, or a bootstrap configuration if nothing is committed on it.""",
    ms=("The pivot", "Take the deepest committed ancestor of the base; if it is not the base itself, the base is uncommitted and the path summary applies between them; without one, follow the base's branch to a bootstrap configuration.")),
"OpenSearchSafety.inv_pub_lcc": dict(
    title="A publication's last committed configuration is a bootstrap configuration or a committed one",
    nl=r"""For all `P`, every cluster `W` with `Inv P W` and every sent publication `W.sent (.publishRequest src s pt pv)`: `P.initConfs s.lastCommittedConfiguration`, or some sent publication `W.sent (.publishRequest src' s' pt' pv')` has `Committed W s'.term s'.version` and `s'.lastAcceptedConfiguration = s.lastCommittedConfiguration`.""",
    ms=None),
"OpenSearchSafety.inv_elc": dict(
    title="Election leader completeness: an election in term t builds on every commit of an earlier term",
    nl=r"""Let `P` satisfy `P.InitCompatible` and let `W` be a cluster with `Inv P W`. Suppose `ElectionRecord P W L t bt bv x y J`: `bt < t`, the configurations `(x, y)` realize the base key `(bt, bv)`, `J` is a quorum of `x` and of `y`, and every member of `J` is an eligible node that sent `L` a join of term `t` whose last accepted term and version are `Below bt bv`. Then every committed key `(ct, cv)` with `ct < t` satisfies `Descends W ct cv bt bv`.

A node that wins term `t` from an accepted state, and the first publication of term `t`, whose parent is that state, build on every publication committed in an earlier term. The proof is a strong induction on `t`: a commit not below the base would have responders sharing a voter with `J` (through the pivot of the base and the configuration lineage, or `P.InitCompatible` when nothing is committed on the base's branch), and that voter accepted the commit before voting in term `t` (`join_after_response`), which places the commit at or below the base.""",
    ms=("Election leader completeness", "Strong induction on the term. Compare the pivot of the base with the commit; the first commit above the pivot has responders that are a quorum of the pivot's accepted configuration, as are the election voters; the common voter accepted the commit before voting, so the commit lies below the base.")),
"OpenSearchSafety.inv_leader_completeness": dict(
    title="Leader completeness: every publication of a later term descends from every committed publication",
    nl=r"""For `P` with `P.InitCompatible`, every cluster `W` with `Inv P W`, every committed key `(t, v)` (`Committed W t v`) and every sent publication `W.sent (.publishRequest src s pt pv)` with `t < s.term`: `Descends W t v s.term s.version`.""",
    ms=None),
"OpenSearchSafety.inv_committed_comparable": dict(
    title="Committed keys are totally ordered by descent",
    nl=r"""For `P` with `P.InitCompatible`, every cluster `W` with `Inv P W` and committed keys `(t₁, v₁)` and `(t₂, v₂)` (`Committed W t₁ v₁`, `Committed W t₂ v₂`): `Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁`.""",
    ms=None),
"OpenSearchSafety.inv_election_quorums": dict(
    title="Two elections of the same term share a voter",
    nl=r"""For `P` with `P.InitCompatible`, every cluster `W` with `Inv P W`, every term `t` and two election records of term `t`, `ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁` and `ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂` (any candidates `L₁`, `L₂`, base keys, configurations and voter lists): some `m` is in both `J₁` and `J₂`.

The two bases have the same pivot (by election leader completeness, each pivot is an ancestor of the other base), whose last accepted configuration both voter lists are quorums of; or neither base has a committed ancestor, and the voter lists are quorums of two bootstrap configurations, which `P.InitCompatible` makes intersect.""",
    ms=("Election quorums intersect", "Both bases have the same pivot, by election leader completeness applied in both directions, so both voter lists are quorums of its accepted configuration; if neither base has a committed ancestor, use the compatibility of the bootstrap configurations.")),
"OpenSearchSafety.inv_election_unique": dict(
    title="Two elections of the same term have the same candidate",
    nl=r"""For `P` with `P.InitCompatible`, every cluster `W` with `Inv P W`, every term `t` and two election records of term `t`, `ElectionRecord P W L₁ t bt₁ bv₁ x₁ y₁ J₁` and `ElectionRecord P W L₂ t bt₂ bv₂ x₂ y₂ J₂`: `L₁ = L₂`. A common voter (`inv_election_quorums`) sent a join of term `t` to `L₁` and one to `L₂`, and an eligible node sends at most one join per term (`join_unique`).""",
    ms=None),
"OpenSearchSafety.inv_init": dict(
    title="A fresh cluster satisfies the invariant",
    nl=r"""For all cluster parameters `P` and every cluster `W` with `Initial P W` (every node `n` is `CoordinationState.init (P.dn n) 0 s` for a term-0 cluster state `s` with empty last committed and last accepted configurations, and no message has been sent): `Inv P W`. No other hypothesis is needed.""",
    ms=None),
"OpenSearchSafety.inv_bootstrap": dict(
    title="The bootstrap step preserves the invariant",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For every node `n`, configuration `X` with `P.initConfs X`, cluster state `s` with `(W.node n).initialStateContract s`, `s.lastCommittedConfiguration = X` and `s.lastAcceptedConfiguration = X`, and state `cs'` with `(W.node n).setInitialState s = .ok cs'`: `Inv P (W.set n cs')`.

These are the hypotheses of the `bootstrap` step; the two hypotheses on `P`, common to all step theorems, are not used here.""",
    ms=None),
"OpenSearchSafety.inv_startJoin": dict(
    title="The startJoin step preserves the invariant",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For all nodes `n` and `src` with `P.eligible src = true`, every term `t`, state `cs'` and join `j` with `(W.node n).handleStartJoin ⟨P.dn src, t⟩ = .ok (cs', j)`: `Inv P ((W.set n cs').send (.join j))`.

The node moves to term `t` and sends its join to `src`. The hypotheses on `P` are not used.""",
    ms=None),
"OpenSearchSafety.inv_join": dict(
    title="The join step preserves the invariant, including when the election is won",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For every node `n`, join `j` with `W.sent (.join j)` and `j.targetNode.id = n`, state `cs'` and flag `b` with `(W.node n).handleJoin P.strategy j = .ok (cs', b)`: `Inv P (W.set n cs')`.

The hard case is a join that wins the election: then no publication of the node's current term exists, its accepted state is of an older term, and no other node has won the term, because two election records of one term have the same candidate (`inv_election_unique`). With the default strategy an election, once won, stays won when votes are added.""",
    ms=("An election win is unique", "When the join wins the election, build the winner's election record from its votes and accepted state; compare it with the record of the first publication of the term and with any other elected node's record using the uniqueness of election records.")),
"OpenSearchSafety.inv_clientValue": dict(
    title="The clientValue step preserves the invariant",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For every node `n`, cluster state `s` with `(W.node n).clientValueContract s`, state `cs'` and publish request `p` with `(W.node n).handleClientValue s = .ok (cs', p)`: `Inv P ((W.set n cs').send (.publishRequest n p.acceptedState (W.node n).lastAcceptedTerm (W.node n).lastAcceptedVersion))`.

The elected node publishes a new state of its term, with its current accepted key as ghost parent. The hypotheses on `P` are not used.""",
    ms=None),
"OpenSearchSafety.inv_publish": dict(
    title="The publish step preserves the invariant",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For all nodes `n` and `src`, every cluster state `s`, term `pt` and version `pv` with `W.sent (.publishRequest src s pt pv)`, and every state `cs'` and response `r` with `(W.node n).handlePublishRequest ⟨s⟩ = .ok (cs', r)`: `Inv P ((W.set n cs').send (.publishResponse n src r))`.

Every publication has term at least 1, so the Zen1 compatibility branch of `handlePublishRequest` never applies; an elected node accepts only its own publication in flight. The hypotheses on `P` are not used.""",
    ms=None),
"OpenSearchSafety.inv_respond": dict(
    title="The respond step preserves the invariant, including commits after a mid-publication commit (D1)",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For all nodes `n` and `src`, every response `r` with `W.sent (.publishResponse src n r)`, and every state `cs'` and optional commit `o` with `(W.node n).handlePublishResponse (P.dn src) r = .ok (cs', o)`: `Inv P W'`, where `W'` is `W.set n cs'` if `o = none`, and `(W.set n cs').send (.applyCommit c)` if `o = some c`.

A new commit is backed by the publish votes, responses to the publication in flight: a quorum of its last accepted configuration and of its last committed configuration, or, when the leader has applied the commit of its accepted state while the publication was in flight, of the configuration of that committed parent. The hypotheses on `P` are not used.""",
    ms=("Commits are backed by quorums", "The publish votes are responses to the leader's publication in flight; the leader's committed and published configurations are that publication's, or the committed parent's accepted configuration after a mid-publication commit.")),
"OpenSearchSafety.inv_commit": dict(
    title="The commit step preserves the invariant, including a leader's mid-publication commit (D1)",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For every node `n`, commit `c` with `W.sent (.applyCommit c)` and state `cs'` with `(W.node n).handleCommit c = .ok cs'`: `Inv P (W.set n cs')`.

Java's `handleCommit` lets an elected node apply the commit of its accepted state while its next publication is in flight (TLA+'s `HandleCommit` forbids it); its last committed configuration then becomes the last accepted one, a case `leader_inflight` records. The hypotheses on `P` are not used.""",
    ms=("The mid-publication commit", "Applying the commit of the leader's accepted state while its next publication is in flight: by the reconfiguration rule of that publication, its accepted configuration is the parent's, or its committed configuration is the parent's accepted one.")),
"OpenSearchSafety.inv_restart": dict(
    title="Restarting a cluster-manager-eligible node preserves the invariant",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For every node `n` with `P.eligible n = true` and every cluster state `s'` with `RestartState (W.node n).lastAcceptedState s'`: `Inv P (W.set n (CoordinationState.init (W.node n).localNode (W.node n).currentTerm s'))`. The hypotheses on `P` are not used.""",
    ms=None),
"OpenSearchSafety.inv_restartAny": dict(
    title="Restarting a node that is not cluster-manager-eligible, with any persisted state, preserves the invariant",
    nl=r"""Let `P` satisfy `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and let `W` satisfy `Inv P W`. For every node `n` with `P.eligible n = false`, every term `t` and every cluster state `s'`: `Inv P (W.set n (CoordinationState.init (W.node n).localNode t s'))`. The hypotheses on `P` are not used.""",
    ms=None),
"OpenSearchSafety.reachable_inv": dict(
    title="The invariant holds in every reachable cluster",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, and every cluster `W` with `Reachable P W`: `Inv P W`.""",
    ms=("The invariant is inductive", "Induction over reachability: the invariant holds initially and each of the nine kinds of step preserves it.")),
"OpenSearchSafety.one_master_per_term": dict(
    title="One cluster-manager per term",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, all nodes `a`, `b`, cluster states `s`, `s'`, terms `pt`, `pt'` and versions `pv`, `pv'`: if `W.sent (.publishRequest a s pt pv)`, `W.sent (.publishRequest b s' pt' pv')` and `s.term = s'.term`, then `a = b`.

Two publications of the same term come from the same node. This is the first property checked by OpenSearch's randomized `CoordinationStateTestCluster`.""",
    ms=("One cluster-manager per term", "Both publishers have `Won` the term (they are eligible and published in it); for each term at most one node has `Won`.")),
"OpenSearchSafety.one_state_per_version": dict(
    title="One cluster state per term and version",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, all nodes `a`, `b`, cluster states `s`, `s'`, terms `pt`, `pt'` and versions `pv`, `pv'`: if `W.sent (.publishRequest a s pt pv)`, `W.sent (.publishRequest b s' pt' pv')`, `s.term = s'.term` and `s.version = s'.version`, then `a = b ∧ s = s' ∧ pt = pt' ∧ pv = pv'`.

Two publications with the same term and version are the same publication: same publisher, same cluster state (all its fields, including the payload), same parent. This is the second property checked by `CoordinationStateTestCluster`. It fails for some non-monotone plugin election strategies when Java assertions are disabled; the hypothesis on the strategy excludes them.""",
    ms=("One state per term and version", "Two publications with the same key are the same message, a field of the invariant.")),
"OpenSearchSafety.leader_completeness": dict(
    title="Leader completeness: every publication of a later term builds on every committed publication",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every key with `Committed W t v`, and every sent publication `W.sent (.publishRequest src s pt pv)` with `t < s.term`: `Descends W t v s.term s.version`.

A cluster-manager of a later term than a committed key publishes only states that descend, through the chain of ghost parents, from that key; publications of the key's own term or of older terms are not covered (a cluster-manager of an older term may even be elected after the commit).""",
    ms=("Leader completeness", "The first publication of the later term carries its publisher's election record; election leader completeness puts the commit below its parent.")),
"OpenSearchSafety.committed_linear": dict(
    title="Committed cluster states never fork",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` (any two bootstrap configurations have intersecting quorums of cluster-manager-eligible nodes) and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, and all keys with `Committed W t₁ v₁` and `Committed W t₂ v₂`: `Descends W t₁ v₁ t₂ v₂ ∨ Descends W t₂ v₂ t₁ v₁`.

Here `Committed W t v` means that an `ApplyCommitRequest` for term `t` and version `v` has been sent, and `Descends` follows the ghost parents of publications: the publication of `(t₂, v₂)` was made on top of an accepted `(t₁, v₁)`, directly or through intermediate publications. Any two committed publications lie on one branch of the history, whatever messages were lost, duplicated, delayed or reordered and whatever nodes restarted: the committed cluster states form a single sequence. With `one_state_per_version`, each committed key names a single cluster state.""",
    ms=None),
"OpenSearchSafety.committed_versions": dict(
    title="A version is committed in at most one term, and committed versions increase with the term",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, and all keys with `Committed W t₁ v₁` and `Committed W t₂ v₂`: `(v₁ = v₂ → t₁ = t₂) ∧ (t₁ < t₂ → v₁ < v₂)`. Two committed publications with the same version have the same term, hence (by `one_state_per_version`) the same cluster state.""",
    ms=None),
"OpenSearchSafety.committed_published": dict(
    title="Every commit is of a publication",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W` and every key with `Committed W t v`: some publication `W.sent (.publishRequest src s pt pv)` with `s.term = t` and `s.version = v` has been sent.""",
    ms=None),
"OpenSearchSafety.election_safety": dict(
    title="Election safety: at any moment, at most one node holds a won election in a given current term",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W` and all nodes `a`, `b` with `(W.node a).electionWon = true`, `(W.node b).electionWon = true` and `(W.node a).currentTerm = (W.node b).currentTerm`: `a = b`.""",
    ms=("Election safety", "Each node holding a won election has `Won` its current term; for each term at most one node has `Won`.")),
"OpenSearchSafety.javaInvariant_reachable": dict(
    title="The assertions of CoordinationState.invariant() never fail at a cluster-manager-eligible node",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W` and every node `n` with `P.eligible n = true`: `(W.node n).javaInvariant P.strategy`.

`javaInvariant` is the conjunction of the five assertions of `invariant()` (`CoordinationState.java:601-611`): the last accepted term is at most the current term; `electionWon` equals `isElectionQuorum` of the join votes; if the election is won, the last published version is at least the last accepted version, otherwise it is 0; a won election implies `startedJoinSinceLastReboot`; the publish votes are empty or the election is won. Not every handler preserves these assertions on its own: `handlePublishRequest` can break them (`OpenSearchCoordination.javaInvariant_not_local`), so they hold because of what the rest of the cluster did. A node that is not cluster-manager-eligible may restart with any persisted state, so the first assertion can fail there.""",
    ms=("invariant() never fails", "Read the five assertions off the node fields of the invariant; for the third, a publication in flight has a larger version than its parent, the accepted state.")),
"OpenSearchSafety.lastCommitted_committed": dict(
    title="Every eligible node's last committed configuration is empty, a bootstrap configuration, or a committed one",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W` and every node `n` with `P.eligible n = true`: `(W.node n).lastCommittedConfiguration = VotingConfiguration.EMPTY_CONFIG` (for instance at a node that has not bootstrapped), or `P.initConfs (W.node n).lastCommittedConfiguration` (a bootstrap configuration), or some sent publication `W.sent (.publishRequest src s pt pv)` with `Committed W s.term s.version` has `s.lastAcceptedConfiguration = (W.node n).lastCommittedConfiguration`.""",
    ms=None),
"OpenSearchSafety.bootstrap_compatible": dict(
    title="Bootstrapping with different partial views gives compatible configurations: two configurations of ClusterBootstrapService's form meet the condition of InitCompatible",
    nl=r"""Let `eligible : NodeId → Bool`, let `k` be the number of bootstrap requirements, and let `resolve placeholder : Nat → NodeId` be such that, for all `i, j < k`: `resolve i = resolve j → i = j` (each requirement names its own node); `placeholder i = placeholder j → i = j`; `placeholder i ≠ resolve j`; and `eligible (placeholder i) = false`. Let `X`, `Y` be configurations and `mX`, `mY : Nat → Bool` with `BootstrapConfig k resolve placeholder mX X` and `BootstrapConfig k resolve placeholder mY Y`. Then for all lists `q₁`, `q₂` of node ids with `eligible x = true` for every `x` in `q₁` and in `q₂`, `X.hasQuorum q₁ = true` and `Y.hasQuorum q₂ = true`, some `x` is in both `q₁` and `q₂`.

Each bootstrapping node uses the configuration of the requirements it has matched, with placeholders for the others, and needs more than half matched (`ClusterBootstrapService`, CBS:176-215, 259-273, 306-335). Different nodes may match different requirements and bootstrap with different configurations; the theorem shows that any two such configurations, built from the same requirements with the same `resolve` and `placeholder` (every requirement resolves to the same node everywhere), meet the condition of `Params.InitCompatible`, the hypothesis of the safety theorems. The theorem does not mention `Params`: `P.InitCompatible` follows for every `P` with `P.eligible = eligible` whose bootstrap configurations are all of this form, but no theorem states this, and the model does not tie `P.initConfs` to `BootstrapConfig`.""",
    ms=("Bootstrap configurations are compatible", "An eligible quorum of such a configuration contains the resolved nodes of more than half of the requirements; two sets of more than half of the requirements share one.")),
"OpenSearchSafety.commit_reachable": dict(
    title="The common hypotheses of the safety theorems can be met together with a commit",
    nl=r"""There exist cluster parameters `P` and a cluster `W` with payload type `Unit` such that `P.InitCompatible`, `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, `Reachable P W` and `Committed W 1 1`.

The hypotheses common to the safety theorems (`P.InitCompatible`, the default strategy, `Reachable P W`) can be met together with a commit. The statement exhibits one committed key and nothing more: neither two distinct committed keys (the non-trivial case of `committed_linear` and `committed_versions`) nor a publication of a later term than a committed key (the hypotheses of `leader_completeness`). In the witness every node is cluster-manager-eligible, the only bootstrap configuration is `{0}`, and node 0 bootstraps, handles a start-join of term 1 from itself, handles its own join (winning the election), publishes the state of term 1 and version 1, accepts it, and handles its own response, which sends the commit of `(1, 1)`.""",
    ms=("Commits happen", "An explicit six-step execution of a one-node cluster.")),
}

ORDER = ["OpenSearchSafety." + k for k in [
    # consequences of the invariant inside one cluster (Sol_OpenSearchSafety_static_all.lean)
    "descends_trans", "inv_descends_key", "inv_descends_parent", "inv_descends_linear", "inv_reign_first",
    "inv_committed_published", "inv_eligible_of_won", "inv_won_of_electionWon", "inv_deepest_committed",
    "inv_first_committed", "inv_first_committed_after", "inv_lineage", "inv_root_lcc", "inv_commit_quorum_after",
    "inv_commit_quorum_first", "inv_pivot", "inv_pub_lcc", "inv_elc", "inv_leader_completeness",
    "inv_committed_comparable", "inv_election_quorums", "inv_election_unique",
    # the invariant initially and under each step (Sol_OpenSearchSafety_steps_all.lean)
    "inv_init", "inv_bootstrap", "inv_startJoin", "inv_join", "inv_clientValue", "inv_publish", "inv_respond",
    "inv_commit", "inv_restart", "inv_restartAny",
    # the public statements (Sol_OpenSearchSafety_all.lean)
    "reachable_inv", "one_master_per_term", "one_state_per_version", "leader_completeness", "committed_linear",
    "committed_versions", "committed_published", "election_safety", "javaInvariant_reachable",
    "lastCommitted_committed", "bootstrap_compatible", "commit_reachable"]]
