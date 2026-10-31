## The claim

OpenSearch (and Elasticsearch since 7.0) keeps the metadata of a cluster — which indices exist, their mappings and settings, which node holds which shard — in a single *cluster state* that one elected node, the **cluster-manager** (formerly "master"), publishes to all others. The algorithm that elects the cluster-manager and makes every published state durable is a Paxos/Raft-like consensus protocol, introduced in Elasticsearch 7.0 as "Zen2". Its core is one class, `CoordinationState`, which every node runs: a state machine with a persisted part (the current term and the last accepted cluster state) and a transient part (election votes, publication votes), driven by seven handlers — `setInitialState`, `handleStartJoin`, `handleJoin`, `handleClientValue`, `handlePublishRequest`, `handlePublishResponse`, `handleCommit`. The class cites Elastic's TLA+ specification `ZenWithTerms` as its formal model; that specification was model-checked on small instances but never proved.

This mission transcribes `CoordinationState` at OpenSearch revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19` and proves its per-node properties. The cluster-level safety theorems (one cluster-manager per term, one state per term and version, committed states never fork, the assertions of `invariant()` never fail) are the next mission; they use the statements proved here.

## The transcription

A node is identified by its id and carries its cluster-manager-eligible role. A **voting configuration** is a set of node ids; a set of votes is a **quorum** of it when it contains more than half of its members (`VotingConfiguration.hasQuorum`). Votes are counted only from cluster-manager-eligible nodes (`VoteCollection.addVote`). A **cluster state** is reduced to the fields `CoordinationState` reads or writes: term, version, metadata version (used instead of the version for term-0 states, `getVersionOrMetadataVersion`), last committed and last accepted configurations, the cluster-manager node (read only by the Zen1 compatibility branch), the cluster-UUID flags, and an opaque payload.

The handlers are transcribed check by check, in the Java order, each returning either a rejection or the new state with its output:

- `handleStartJoin` moves to a strictly higher term and votes (a `Join`) for the requesting node, carrying the node's last accepted term and version;
- `handleJoin` counts a vote for the current term from a voter whose accepted state is no fresher than the node's own, and recomputes `electionWon` as "the votes are a quorum of both the last committed and the last accepted configuration" (plus a pluggable election-strategy constraint);
- `handleClientValue` lets an elected node publish a new state of its term with a higher version, reconfiguring only when no reconfiguration is pending and only to a configuration in which its votes are a quorum;
- `handlePublishRequest` accepts a state of the current term that is newer than the last accepted one;
- `handlePublishResponse` counts publication votes and emits an `ApplyCommitRequest` once they are a quorum of both the last committed configuration and the configuration being published;
- `handleCommit` marks the last accepted state committed (its accepted configuration becomes the committed one).

Java `assert`s are disabled in production and are caller contracts; the transcription does not check them, and the cluster model of the next mission states them as preconditions of the steps that call these methods. The remote cluster-state store (`RemotePersistedState`) is written but never read by these handlers and is omitted.

## What is proved

- **Quorums**: two quorums of the same configuration intersect; a superset of a quorum is a quorum; the empty configuration has no quorum; no votes are no quorum; only eligible votes count.
- **Handler specifications**: what each handler requires and changes (`handleStartJoin_spec`, `handleJoin_spec`, `handleClientValue_spec`, `handlePublishRequest_spec`, `handlePublishResponse_spec`, `handleCommit_spec`).
- **Monotonicity**: only `handleStartJoin` changes the current term, and only upwards; the accepted state of a node moves strictly forward in the (term, version) order except in the Zen1 compatibility branch; the last accepted term never exceeds the current term.
- **Elections**: a node only counts votes from voters whose accepted state is no fresher than its own; for a monotone election strategy (the default is) a won election stays won — the assertion at `CoordinationState.java:323-324`.
- **The assertions of `invariant()`**: they hold for a freshly started node and are preserved by `handleStartJoin`, `handleJoin`, `handleClientValue` and `handlePublishResponse`, but **not** by `handlePublishRequest` in isolation: an explicit node satisfies `invariant()`, accepts a publication, and violates it. That `invariant()` holds at every node of every execution is therefore a property of the whole cluster, proved in the next mission.

## What this rests on

The Java source at the pinned revision: `CoordinationState.java`, `CoordinationMetadata.java` (`VotingConfiguration`), `ElectionStrategy.java`, `ClusterState.java` (`getVersionOrMetadataVersion`), and the message classes. Terms are natural numbers (they start at 0 and only increase); versions are integers (Java `long`; overflow is not modelled). Only `Std` is imported.
