# Read-back: `OpenSearchCoordination.handleStartJoin_spec`

## Notions used

**Coordination states and cluster states.** For a payload type $V$, a coordination state $cs$ has nine fields:

- $cs.\mathrm{localNode}$: a node, made of an id in $\mathbb{N}$ and a Boolean "eligible" flag `isClusterManagerNode`;
- $cs.\mathrm{currentTerm} \in \mathbb{N}$;
- $cs.\mathrm{lastAcceptedState}$: a cluster state;
- $cs.\mathrm{joinVotes}$ and $cs.\mathrm{publishVotes}$: vote collections, which are lists of ids;
- $cs.\mathrm{startedJoinSinceLastReboot}$ and $cs.\mathrm{electionWon}$: Booleans;
- $cs.\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $cs.\mathrm{lastPublishedConfiguration}$: a voting configuration.

A cluster state $S$ has:

- $S.\mathrm{term} \in \mathbb{N}$;
- $S.\mathrm{version}, S.\mathrm{metadataVersion} \in \mathbb{Z}$;
- two voting configurations, $S.\mathrm{lastCommittedConfiguration}$ and $S.\mathrm{lastAcceptedConfiguration}$;
- an optional natural $S.\mathrm{clusterManagerNode}$;
- two Booleans about the cluster UUID;
- a payload $S.\mathrm{value} \in V$.

The file's accessors give these abbreviations:

- $\mathrm{lat}(cs) = cs.\mathrm{lastAcceptedState}.\mathrm{term}$;
- $\mathrm{A}(cs) = cs.\mathrm{lastAcceptedState}.\mathrm{lastAcceptedConfiguration}$;
- $\mathrm{lavm}(cs)$ is the accepted state's $\mathrm{metadataVersion}$ if its term is $0$, and its $\mathrm{version}$ otherwise (`lastAcceptedVersionOrMetadataVersion`).

$\mathrm{VoteCollection.empty}$ is the empty list.

**Messages.** A start-join request $r$ has a node $r.\mathrm{sourceNode}$ and a term $r.\mathrm{term} \in \mathbb{N}$. A join is a 5-tuple $\langle \mathrm{sourceNode}, \mathrm{targetNode}, \mathrm{term}, \mathrm{lastAcceptedTerm}, \mathrm{lastAcceptedVersion}\rangle$ of two nodes, two naturals and an integer.

**The handler** $\mathrm{handleStartJoin}(cs, r)$:

- If $r.\mathrm{term} \le cs.\mathrm{currentTerm}$, it returns $\mathrm{error}$.
- Otherwise it returns $\mathrm{ok}(cs^\ast, J)$, where:
  - $cs^\ast$ is $cs$ with $\mathrm{currentTerm} := r.\mathrm{term}$, $\mathrm{lastPublishedVersion} := 0$, $\mathrm{lastPublishedConfiguration} := \mathrm{A}(cs)$, $\mathrm{startedJoinSinceLastReboot} := \mathrm{true}$, $\mathrm{electionWon} := \mathrm{false}$, $\mathrm{joinVotes} := \mathrm{empty}$ and $\mathrm{publishVotes} := \mathrm{empty}$;
  - $J = \langle cs.\mathrm{localNode},\ r.\mathrm{sourceNode},\ r.\mathrm{term},\ \mathrm{lat}(cs),\ \mathrm{lavm}(cs)\rangle$.

## 1. Declaration

**Binders.**
- $V$: a type (implicit);
- $cs$: a coordination state over $V$;
- $r$ (`req`): a start-join request;
- $cs'$: a coordination state over $V$;
- $j$: a join.

**Hypotheses.** None.

**Conclusion.** The statement is a biconditional:
$$\mathrm{handleStartJoin}(cs, r) = \mathrm{ok}(cs', j) \iff (1) \wedge \dots \wedge (11),$$
where:

1. $cs.\mathrm{currentTerm} < r.\mathrm{term}$;
2. $cs'.\mathrm{currentTerm} = r.\mathrm{term}$;
3. $cs'.\mathrm{lastAcceptedState} = cs.\mathrm{lastAcceptedState}$;
4. $cs'.\mathrm{localNode} = cs.\mathrm{localNode}$;
5. $cs'.\mathrm{startedJoinSinceLastReboot} = \mathrm{true}$;
6. $cs'.\mathrm{electionWon} = \mathrm{false}$;
7. $cs'.\mathrm{joinVotes} = \mathrm{VoteCollection.empty}$;
8. $cs'.\mathrm{publishVotes} = \mathrm{VoteCollection.empty}$;
9. $cs'.\mathrm{lastPublishedVersion} = 0$;
10. $cs'.\mathrm{lastPublishedConfiguration} = \mathrm{A}(cs)$;
11. $j = \langle cs.\mathrm{localNode},\ r.\mathrm{sourceNode},\ r.\mathrm{term},\ \mathrm{lat}(cs),\ \mathrm{lavm}(cs)\rangle$.

Conjuncts 2–10 fix all nine fields of $cs'$, and conjunct 11 fixes $j$. So the right-hand side says exactly that the guard holds and that $(cs', j)$ is the handler's output.

The biconditional therefore characterizes the handler completely:

- It succeeds iff $r.\mathrm{term} > cs.\mathrm{currentTerm}$, and its output is then the one listed.
- When $r.\mathrm{term} \le cs.\mathrm{currentTerm}$ the result is not $\mathrm{ok}$ of anything, so it is an $\mathrm{error}$.

## 2. What is not constrained

- $cs$ is arbitrary. No invariant is assumed. In particular, $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$ is not required.
- $r.\mathrm{sourceNode}$ is arbitrary. It may be the local node itself, and it may be ineligible. It appears only as the target of the returned join.
- The old $\mathrm{joinVotes}$, $\mathrm{publishVotes}$, $\mathrm{electionWon}$ and $\mathrm{lastPublishedVersion}$ are discarded whatever their values.
- The join's version field is $\mathrm{lavm}(cs)$: the metadata version when the accepted state's term is $0$, otherwise the cluster-state version.
- There are no hypotheses, so nothing can make the statement vacuous. Both sides of the biconditional are satisfiable.

## 3. Plain-language summary

A start-join request succeeds exactly when its term is larger than the node's current term. The node then:

- adopts that term;
- keeps its accepted state and identity;
- resets its election and publication bookkeeping: votes emptied, election not won, published version $0$, published configuration set to the accepted configuration;
- records that it has started a join since restart.

It returns a join vote from itself to the requester, carrying the new term and its last accepted term and version (the metadata version for term-0 states).
