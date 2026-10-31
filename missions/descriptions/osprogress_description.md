## The claim

The safety mission proves that OpenSearch's cluster coordination never forks, whatever the network does: messages lost, duplicated, delayed or reordered, nodes restarting. Progress cannot be proved in that generality. In that model a message may never be delivered, and nothing stops candidates from starting elections in ever higher terms, each start-join discarding the votes and the leadership of the term before. The obstacle is fundamental: Fischer, Lynch and Paterson showed that no deterministic consensus protocol can guarantee termination in an asynchronous network in which a single node may crash. Protocols of the Paxos and Raft family, OpenSearch's included, are designed to be safe always and to make progress when the system behaves well for long enough (partial synchrony, in the terms of Dwork, Lynch and Stockmeyer). OpenSearch makes such periods likely with pre-voting, which keeps nodes that cannot win from starting elections, and with randomized election timers, which make it likely that one candidate runs alone; both are the subject of other missions.

This mission states progress for the executions of a *stable period*: a window in which one node runs for election, or publishes a cluster state, and nothing disrupts it, while every other step of the cluster model remains possible. It proves that in every such execution the steps the protocol needs stay enabled, that once they have happened the election is won (the publication is committed), and that such executions exist. The model, the steps and the safety invariant are those of the safety mission, over the transcribed `CoordinationState` of OpenSearch revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`.

## The stable periods

A stable step is a step of the safety model with, for some kinds of step, an extra condition; so every stable execution from a reachable cluster stays reachable, and the safety invariant holds along it.

**A stable election** for a candidate `c` in term `t` with voters `Q`, writing `(kt, kv)` for the term and version of `c`'s accepted state when the period starts, excludes:
- a start-join request in a term at least `t`, at any node, other than `c`'s own request for `t`: no competing candidate for `t` or a higher term;
- any new publication;
- a bootstrap or a restart of `c` or of a voter;
- the acceptance, by `c` or by a voter, of a publication fresher than `(kt, kv)`: a stale publication of a former cluster-manager arriving during the election, which would make the voter's join fresher than `c`'s state, and hence rejected.

Everything else remains possible, in any order and any number of times: the delivery of joins, publish responses and commits to any node; the acceptance of publications no fresher than `(kt, kv)` by the voters, and of any publication by the other nodes; start-join requests of lower terms at any node, voters included; commits at `c` and at the voters; bootstraps and restarts of the other nodes.

**A stable publication** for the cluster-manager `c` of term `t` with acknowledging nodes `Q` excludes:
- a start-join request in a term above `t` at `c` or at a node of `Q`;
- a further publication by `c`;
- a restart of `c`.

Everything else remains possible: start-join requests of any term at the other nodes and of terms up to `t` at the nodes of `Q` (which lets them reach term `t`), publications by other nodes (a stale cluster-manager of an older term), the acceptance of any publication by any node, joins, commits (at `c` too, while its publication is in flight), bootstraps, and restarts of every node other than `c`, the nodes of `Q` included.

## What is proved

Every theorem starts from a reachable cluster and assumes, as the safety theorems do, compatible bootstrap configurations and OpenSearch's default election strategy.

- **Elections.** Let `c` and the voters `Q` be cluster-manager-eligible and in terms below `t`, with every voter's accepted state no fresher than `c`'s (compared as `handleJoin` compares them).
  - `election_vote_accepted`: in every stable election execution, once `c` is in term `t`, `c` accepts every voter's join for `t` whenever it arrives, and counts the vote.
  - `election_won`: if `Q` is a quorum of both of `c`'s configurations, `c` has won as soon as it is in term `t` and has counted the votes of all of `Q`, whatever else happened in the period.
  - `election_possible` (the goal): there is a stable election execution, in which `c` and each voter handle `c`'s start-join request for `t` and `c` handles the voters' joins, at the end of which `c` has won.
- **Publications.** Let `c` be elected in term `t`, with `s` its latest publication, and `Q` cluster-manager-eligible.
  - `publication_acks_accepted`: in every stable publication execution, every node of `Q` in term `t` has already acknowledged `s` or accepts it now, and `c` accepts and counts every acknowledgement of `s` from a node of `Q`, whenever it arrives.
  - `publication_committed`: if `Q` is a quorum of `c`'s two configurations and of `s`'s two configurations, and `c` has counted no acknowledgement yet (as right after publishing), the publication is committed as soon as `c` has counted the acknowledgements of all of `Q`.
  - `publication_possible`: if moreover the nodes of `Q` are in terms at most `t`, there is a stable publication execution, in which each node of `Q` moves to term `t` if needed and accepts and acknowledges `s` and `c` counts the acknowledgements, at the end of which the publication is committed.

The witness executions show that the premises of `election_won` and `publication_committed` are reached: the restrictions of a stable period leave enabled every step an election and a publication need, so these theorems are not vacuous.

**Why four configurations.** A cluster-manager commits when its publish votes are a quorum of its *current* last committed configuration and of the configuration being published. Java's `handleCommit` lets it apply the commit of its accepted state while its next publication is in flight (the behaviour, called D1, by which the safety mission's model departs from Elastic's TLA+ model); its last committed configuration then becomes its last accepted one, and when it later accepts its own publication `s` it becomes `s`'s last committed configuration again: it moves backwards. For example, let `s` carry the last committed configuration {1,2,3} and the last accepted configuration {1,2,4}, a reconfiguration in flight, and let the cluster-manager 1 have applied the commit of its accepted state, so that its own last committed configuration is {1,2,4}. With `Q` = {2,4}, a quorum of {1,2,4} but not of {1,2,3}: if node 1 accepts `s` before counting the acknowledgements of nodes 2 and 4, its last committed configuration is {1,2,3} again, and all of `Q` is counted without a commit. `publication_committed` therefore asks `Q` to be a quorum of every configuration the cluster-manager may be using when the last acknowledgement arrives: its own two and the published state's two.

The proofs rest on the safety mission's invariant, which supplies, for instance, that a node that has not won holds no quorum of both its configurations, and that every publication of the cluster-manager's term is its own, with a version at most its last published version. Since a node has always acknowledged the publication it holds, a node of `Q` that rejects `s` has therefore already acknowledged it.

## What this rests on and what it does not say

The safety mission's model and inductive invariant (its definitions are imported, and its theorems used as published), the per-node transcription of `CoordinationState`, and the argument of the safety mission that the [`Coordinator`](https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java)'s calls are steps of the model.

- **A stable period is a hypothesis.** Nothing says that a real network reaches one, how long it lasts or how long its steps take: the model has no time. The theorems are about finite executions; that progress eventually happens follows only under the informal assumption that the needed deliveries take place while the period lasts.
- **The links to the other missions are informal.** A pre-voting round that has started an election establishes the election hypotheses (a quorum of voters no fresher than the candidate, in terms below the new term) if its senders have not changed since answering, and randomized timers make it likely that a candidate fires well before the others; neither link is a composed theorem.
- **Failure detection is not modelled.** The `LeaderChecker` and `FollowersChecker`, through which nodes notice a failed cluster-manager or follower and become candidates, and the publication timeouts are outside the model.
- **Inherited assumptions.** Compatible bootstrap configurations, the default election strategy, and the safety mission's assumptions (fixed roles, no disk rollback, no offline tools, exact remote publication) and per-node abstractions.
