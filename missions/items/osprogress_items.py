SRC = ("OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: Coordinator (handlePublishRequest lines 454-526 with ensureTermAtLeast "
       "at 512, startElection 583-602, ensureTermAtLeast 635-641, joinLeaderInTerm 643-657, handleJoin 1267-1299, publish 1350 with "
       "the handleClientValue call at 1404, CoordinatorPublication.handlePublishResponse 1871-1876): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; "
       "CoordinationState (isPublishQuorum lines 156-158, handleStartJoin 213-255, handleJoin 264-339, handleClientValue 348-407, "
       "handlePublishRequest 416-460, handlePublishResponse 471-515, handleCommit 523-573) as transcribed by the OpenSearchCoordination mission: "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/CoordinationState.java; "
       "the cluster model, the safety vocabulary and the inductive invariant of the OpenSearchSafety mission (Step, Reachable, Committed, Inv, reachable_inv); "
       "for why progress needs a stable period: M. J. Fischer, N. A. Lynch, M. S. Paterson, Impossibility of distributed consensus with one faulty process, "
       "J. ACM 32(2), 1985, and C. Dwork, N. Lynch, L. Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35(2), 1988")
TAGS = ["opensearch", "elasticsearch", "consensus", "cluster-coordination", "zen2", "raft", "paxos", "liveness", "progress",
        "leader-election", "publication", "partial-synchrony", "message-passing", "formal-verification"]

DEFINITION = {
    "definition_name": "OpenSearchProgress",
    "definition_title": "OpenSearch cluster coordination in a stable period: the steps and executions of a stable election and of a stable publication",
    "natural_language_statement": r"""Stable periods of the cluster model of the `OpenSearchSafety` mission (OpenSearch revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`), whose `Params`, `Cluster`, `Message`, `Step`, `RestartState`, `Reachable` and `Committed` are used as they are, over the per-node `CoordinationState` of the `OpenSearchCoordination` mission. A stable period is a window in which one node runs for election (or publishes) and nothing disrupts it, while every other step of the cluster remains possible. Each stable step is one of the nine kinds of `Step` (`bootstrap`, `startJoin`, `join`, `clientValue`, `publish`, `respond`, `commit`, `restart`, `restartAny`), with the same hypotheses and the same effect, and possibly an extra hypothesis.

**`ElectionStep P c t Q kt kv W W'`** — a step of a stable election period for the candidate `c` in term `t` with voters `Q` (a list of node ids), where `(kt, kv)` stands for the term and version of `c`'s accepted state when the period starts:
- `bootstrap` at a node `n` only if `n ≠ c` and `n ∉ Q`;
- `startJoin` (any node handling a request from a cluster-manager-eligible `src` for a term `t'`) only if `t' < t`, or `src = c` and `t' = t`: no start-join request in a term at least `t` other than `c`'s own request for `t`;
- `join`, `respond` and `commit` as in `Step`;
- `publish` (a node `n` handling a sent publication of a state `s`) only if, when `n = c` or `n ∈ Q`, `s` is no fresher than `(kt, kv)`: `s.term < kt`, or `s.term = kt` and `s.version ≤ kv` (`c` and the voters do not accept a stale publication of a former cluster-manager that is fresher than `c`'s state);
- `restart` of a cluster-manager-eligible node `n` only if `n ≠ c` and `n ∉ Q`; `restartAny` (a node that is not cluster-manager-eligible) as in `Step`;
- no `clientValue` step: no new publication.

**`ElectionExec P c t Q kt kv W W'`** — `W'` is reached from `W` by finitely many, possibly zero, `ElectionStep`s.

**`PublicationStep P c t Q W W'`** — a step of a stable publication period for the cluster-manager `c` of term `t` with acknowledging nodes `Q`:
- `startJoin` at a node `n` with `n = c` or `n ∈ Q` only for terms `t' ≤ t` (at other nodes, any term);
- `clientValue` only at nodes `n ≠ c`: `c` does not publish again;
- `restart` of a cluster-manager-eligible node `n` only if `n ≠ c`;
- `bootstrap`, `join`, `publish`, `respond`, `commit` and `restartAny` as in `Step`.

**`PublicationExec P c t Q W W'`** — `W'` is reached from `W` by finitely many, possibly zero, `PublicationStep`s.

**Formalization Note.** Every stable step is a `Step` of the safety model, so a stable execution from a reachable cluster stays reachable and the safety theorems apply along it. Messages are still never removed: within a stable period a sent message may be handled any number of times, in any order, or never, and the theorems hold for every finite stable execution, that is, every prefix of a longer one; there is no fairness assumption. A stable period is a hypothesis of the theorems, not a property of the Java system: nothing here says that a real cluster reaches such a period, for how long it lasts, or how long its steps take. The parameters `(kt, kv)` of the election period are instantiated in the theorems with `c`'s last accepted term and version at the start. A voter may be the candidate itself, and `Q` may contain `c` in a publication period. Only the `OpenSearchSafety` definitions are imported (Lean core).""",
}

THEOREMS = {
"OpenSearchProgress.election_vote_accepted": dict(
    title="Votes keep counting during a stable election: the candidate accepts every voter's join whenever it arrives",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list of node ids `Q` such that

- `c` and every member of `Q` are cluster-manager-eligible: `P.eligible c = true` and `P.eligible q = true` for every `q ∈ Q`;
- `c` and every member of `Q` are in a term below `t`: `(W.node q).currentTerm < t` for `q = c` and for every `q ∈ Q`;
- every member of `Q` has an accepted state no fresher than `c`'s, compared as `handleJoin` compares a join with the node's state: `(W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm`, or the two terms are equal and `(W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion`;
- `c` has been bootstrapped: `(W.node c).lastAcceptedConfiguration.isEmpty = false`;

and every cluster `W'` with `ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W'` (a stable election period for `c`, `t` and `Q` starting at `W`) in which `c` is in term `t`, `(W'.node c).currentTerm = t`: for every join `j` with `W'.sent (.join j)`, `j.sourceNode.id ∈ Q`, `j.targetNode.id = c` and `j.term = t`, there are a state `cs'` and a flag `b` with `(W'.node c).handleJoin P.strategy j = .ok (cs', b)` and `j.sourceNode.id ∈ cs'.joinVotes.nodes`.

Whatever has happened since the period started (deliveries in any order, duplicates, the other nodes' steps, commits at `c` and at the voters), each voter's join for `t` is accepted by `c` whenever it is delivered, and the vote is counted.""",
    ms=("Votes keep counting", "Along a stable election the candidate's accepted state keeps its term, version and accepted configuration, and every voter's state and join for t stay no fresher than it; so once the candidate is in term t every check of handleJoin passes.")),
"OpenSearchProgress.election_won": dict(
    title="A stable election is won once the votes of a quorum are counted",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list of node ids `Q` such that

- `c` and every member of `Q` are cluster-manager-eligible;
- `Q` is a quorum of both of `c`'s configurations: `(W.node c).lastCommittedConfiguration.hasQuorum Q = true` and `(W.node c).lastAcceptedConfiguration.hasQuorum Q = true`;
- `c` and every member of `Q` are in a term below `t`: `(W.node q).currentTerm < t` for `q = c` and for every `q ∈ Q`;

and every cluster `W'` with `ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W'` such that `(W'.node c).currentTerm = t` and every member of `Q` is among `c`'s join votes (`q ∈ (W'.node c).joinVotes.nodes` for every `q ∈ Q`): `(W'.node c).electionWon = true`.

No hypothesis on the voters' accepted states is needed: the votes are already counted. During the period `c`'s committed configuration may change by a commit, but only to its accepted configuration, of which `Q` is also a quorum.""",
    ms=("A stable election is won", "A node that has not won holds no quorum of both its configurations (a field of the safety invariant), while the candidate's configurations are unchanged up to a commit and its votes contain Q.")),
"OpenSearchProgress.election_possible": dict(
    title="Stable elections succeed: some stable election execution ends with the candidate elected",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list of node ids `Q` such that

- `c` and every member of `Q` are cluster-manager-eligible;
- `Q` is a quorum of `(W.node c).lastCommittedConfiguration` and of `(W.node c).lastAcceptedConfiguration`;
- `c` and every member of `Q` are in a term below `t`;
- every member of `Q` has an accepted state no fresher than `c`'s: `(W.node q).lastAcceptedTerm < (W.node c).lastAcceptedTerm`, or the terms are equal and `(W.node q).lastAcceptedVersionOrMetadataVersion ≤ (W.node c).lastAcceptedVersionOrMetadataVersion`;

there is a cluster `W'` with `ElectionExec P c t Q (W.node c).lastAcceptedTerm (W.node c).lastAcceptedVersion W W'`, `(W'.node c).currentTerm = t` and `(W'.node c).electionWon = true`.

In the witness, `c` handles its own start-join request for `t`, every voter not yet in term `t` handles it and sends its join, and `c` handles every voter's join. The restrictions of the stable period leave enabled every step an election needs, so the premises of `election_won` are reached.""",
    ms=("Stable elections succeed", "An explicit stable execution: the candidate's own start-join for t, each voter's start-join, then each voter's join handled and counted.")),
"OpenSearchProgress.publication_acks_accepted": dict(
    title="Acknowledgements keep counting during a stable publication",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list `Q` of cluster-manager-eligible node ids, such that `c` has won the election and is in term `t` (`(W.node c).electionWon = true`, `(W.node c).currentTerm = t`), every cluster state `s`, term `pt` and version `pv` such that `c` has sent the publication of `s` with ghost parent `(pt, pv)` (`W.sent (.publishRequest c s pt pv)`), `s.term = t` and `s.version = (W.node c).lastPublishedVersion` (it is `c`'s latest publication), and every cluster `W'` with `PublicationExec P c t Q W W'`:

1. every `q ∈ Q` with `(W'.node q).currentTerm = t` has already acknowledged `(t, s.version)` to `c` (`W'.sent (.publishResponse q c ⟨t, s.version⟩)`) or accepts `s` now: `(W'.node q).handlePublishRequest ⟨s⟩ = .ok (cs', r)` for some `cs'` and `r`;
2. for every `q ∈ Q` with `W'.sent (.publishResponse q c ⟨t, s.version⟩)`, `c` accepts that acknowledgement and counts it: `(W'.node c).handlePublishResponse (P.dn q) ⟨t, s.version⟩ = .ok (cs', o)` for some `cs'` and `o` with `q ∈ cs'.publishVotes.nodes`.

A node of `Q` that has not reached term `t` can do so in the period by handling a start-join from `c` for `t`, as `Coordinator.ensureTermAtLeast` does when a node receives a publication of a higher term.""",
    ms=("Acknowledgements keep counting", "Along a stable publication the cluster-manager stays elected in term t with the same last published version; a node of term t that rejects the publication already holds it and has acknowledged it, since the only publication of term t at that version is the cluster-manager's.")),
"OpenSearchProgress.publication_committed": dict(
    title="A stable publication is committed once a quorum's acknowledgements are counted",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list `Q` of cluster-manager-eligible node ids, such that `c` has won the election and is in term `t`, every cluster state `s`, term `pt` and version `pv` with `W.sent (.publishRequest c s pt pv)`, `s.term = t` and `s.version = (W.node c).lastPublishedVersion`, such that moreover

- `Q` is a quorum of four configurations: `c`'s last committed and last accepted configurations (`(W.node c).lastCommittedConfiguration.hasQuorum Q = true`, `(W.node c).lastAcceptedConfiguration.hasQuorum Q = true`) and the published state's (`s.lastCommittedConfiguration.hasQuorum Q = true`, `s.lastAcceptedConfiguration.hasQuorum Q = true`);
- `c` has counted no acknowledgement yet: `(W.node c).publishVotes.nodes = []`, as right after `handleClientValue`, which empties the publish votes;

and every cluster `W'` with `PublicationExec P c t Q W W'` in which every member of `Q` is among `c`'s publish votes (`q ∈ (W'.node c).publishVotes.nodes` for every `q ∈ Q`): `Committed W' t s.version`, that is, an `ApplyCommitRequest` for term `t` and version `s.version` has been sent.

`handlePublishResponse` sends the commit when the votes are a quorum of `c`'s current last committed configuration and of the configuration being published (`isPublishQuorum`, `CoordinationState.java:156-158`). During the period `c`'s last committed configuration can change: applying the commit of its accepted state makes it `c`'s last accepted configuration (Java's `handleCommit` allows this while a publication is in flight), and accepting its own publication makes it `s`'s last committed configuration, which can move it backwards. `Q` must therefore be a quorum of every configuration `c` may be using when the acknowledgement that completes `Q` arrives; otherwise all of `Q` could be counted without a commit.""",
    ms=None),
"OpenSearchProgress.publication_possible": dict(
    title="Stable publications are committed: some stable publication execution reaches the commit",
    nl=r"""For every payload type `V`, cluster parameters `P` with `P.InitCompatible` and `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`, every cluster `W` with `Reachable P W`, every node `c`, term `t` and list `Q` of cluster-manager-eligible node ids, such that `c` has won the election and is in term `t`, every cluster state `s`, term `pt` and version `pv` with `W.sent (.publishRequest c s pt pv)`, `s.term = t` and `s.version = (W.node c).lastPublishedVersion`, such that

- `Q` is a quorum of `(W.node c).lastCommittedConfiguration`, `(W.node c).lastAcceptedConfiguration`, `s.lastCommittedConfiguration` and `s.lastAcceptedConfiguration`;
- every member of `Q` is in a term at most `t`: `(W.node q).currentTerm ≤ t` for every `q ∈ Q`;

there is a cluster `W'` with `PublicationExec P c t Q W W'` and `Committed W' t s.version`. Unlike `publication_committed`, `c` may already have counted acknowledgements at `W`.

In the witness, each node of `Q` below term `t` handles a start-join from `c` for `t`, each node of `Q` accepts `s` and acknowledges it unless it already has, and `c` counts the acknowledgements; the restrictions of the stable period leave every such step enabled.""",
    ms=("Stable publications are committed", "An explicit stable execution: each node of Q moves to term t and accepts, the cluster-manager counts every acknowledgement, and one more acknowledgement finds a publish quorum.")),
}
ORDER = ["OpenSearchProgress." + k for k in ["election_vote_accepted", "election_won", "election_possible",
  "publication_acks_accepted", "publication_committed", "publication_possible"]]
