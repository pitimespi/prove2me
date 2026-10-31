# Read-back: `OpenSearchCoordination.handleClientValue_spec`

## Notions used

**Coordination states and cluster states.** For a payload type $V$, a coordination state $cs$ has nine fields:

- $cs.\mathrm{localNode}$;
- $cs.\mathrm{currentTerm} \in \mathbb{N}$;
- $cs.\mathrm{lastAcceptedState}$, a cluster state;
- $cs.\mathrm{joinVotes}$ and $cs.\mathrm{publishVotes}$, vote collections (lists of ids);
- $cs.\mathrm{startedJoinSinceLastReboot}$ and $cs.\mathrm{electionWon}$, Booleans;
- $cs.\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $cs.\mathrm{lastPublishedConfiguration}$.

A cluster state $S$ has nine independent fields:

- $S.\mathrm{term} \in \mathbb{N}$;
- $S.\mathrm{version}, S.\mathrm{metadataVersion} \in \mathbb{Z}$;
- two voting configurations, $S.\mathrm{lastCommittedConfiguration}$ and $S.\mathrm{lastAcceptedConfiguration}$;
- an optional cluster-manager id;
- two Booleans about the cluster UUID;
- a payload.

Abbreviations, all read from the accepted state:

- $\mathrm{lav}(cs) = cs.\mathrm{lastAcceptedState}.\mathrm{version}$;
- $\mathrm{C}(cs)$ is the last committed configuration;
- $\mathrm{A}(cs)$ is the last accepted configuration.

**Configurations and votes.**

- Voting configurations are strictly increasing lists of ids. Two configurations are equal iff they denote the same set.
- $\mathrm{isQuorum}(v, c)$ holds iff $2\,|\{x \in c.\mathrm{nodeIds} : x \in v.\mathrm{nodes}\}| > |c.\mathrm{nodeIds}|$.
- $\mathrm{VoteCollection.empty}$ is the empty list.

A publish request is a wrapper $\langle S\rangle$ around one cluster state.

**The handler** $\mathrm{handleClientValue}(cs, S)$ tests six guards in order. The first one that holds yields $\mathrm{error}$:

1. $\neg cs.\mathrm{electionWon}$;
2. $cs.\mathrm{lastPublishedVersion} \ne \mathrm{lav}(cs)$;
3. $S.\mathrm{term} \ne cs.\mathrm{currentTerm}$;
4. $S.\mathrm{version} \le cs.\mathrm{lastPublishedVersion}$;
5. $S.\mathrm{lastAcceptedConfiguration} \ne \mathrm{A}(cs) \wedge \mathrm{C}(cs) \ne \mathrm{A}(cs)$;
6. $\neg\mathrm{isQuorum}(cs.\mathrm{joinVotes}, S.\mathrm{lastAcceptedConfiguration})$.

If no guard holds, the result is
$$\mathrm{ok}\big(cs \text{ with } \mathrm{lastPublishedVersion} := S.\mathrm{version},\ \mathrm{lastPublishedConfiguration} := S.\mathrm{lastAcceptedConfiguration},\ \mathrm{publishVotes} := \mathrm{empty};\ \langle S\rangle\big).$$

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $cs$: a coordination state;
- $S$ (`s`): a cluster state;
- $cs'$: a coordination state;
- $p$: a publish request.

**Hypothesis.** $h$: $\mathrm{handleClientValue}(cs, S) = \mathrm{ok}(cs', p)$.

**Conclusion.** The conjunction of:

1. $cs.\mathrm{electionWon} = \mathrm{true}$;
2. $cs.\mathrm{lastPublishedVersion} = \mathrm{lav}(cs)$;
3. $S.\mathrm{term} = cs.\mathrm{currentTerm}$;
4. $\mathrm{lav}(cs) < S.\mathrm{version}$;
5. $S.\mathrm{lastAcceptedConfiguration} = \mathrm{A}(cs)\ \vee\ \mathrm{C}(cs) = \mathrm{A}(cs)$;
6. $\mathrm{isQuorum}(cs.\mathrm{joinVotes}, S.\mathrm{lastAcceptedConfiguration}) = \mathrm{true}$;
7. $p = \langle S\rangle$;
8. $cs' = cs$ with $\mathrm{lastPublishedVersion} := S.\mathrm{version}$, $\mathrm{lastPublishedConfiguration} := S.\mathrm{lastAcceptedConfiguration}$ and $\mathrm{publishVotes} := \mathrm{VoteCollection.empty}$.

Conjuncts 1–6 are the negations of the six guards. Conjunct 4 is stated against $\mathrm{lav}(cs)$ rather than $cs.\mathrm{lastPublishedVersion}$; given conjunct 2 the two are equivalent. Conjunct 5 means: either the value keeps the accepted configuration, or no reconfiguration is pending. Conjuncts 7 and 8 determine the output completely.

## 2. What is not constrained

- **The committed configuration of $S$ is free.** $S.\mathrm{lastCommittedConfiguration}$ appears in neither the hypotheses nor the conclusion. The handler does not check it. Java's assertion that it equals $\mathrm{C}(cs)$ is the separate predicate `clientValueContract`, which is not used here. So the statement allows publishing a value whose committed configuration differs from the node's.
- **Other fields of $S$ are free:** $S.\mathrm{metadataVersion}$, the cluster-manager id, the UUID flags and the payload.
- **The configuration test is set equality.** "Equal" in conjunct 5 compares sets, because configurations are stored sorted.
- **No hypothesis on $cs$** beyond success, and no invariant.
- **Only one direction.** The statement goes from success to the conjuncts. It does not claim that a value meeting 1–6 is accepted, although by definition it is.
- **Not vacuous.** For example, a winner with matching versions, given a value of the current term with a higher version and the same accepted configuration, satisfies the hypothesis whenever its join votes are a quorum of that configuration.

## 3. Plain-language summary

A node accepts a new cluster state for publication only if all of the following hold:

- it has won the election;
- its previous publication has been accepted locally (published version equals accepted version);
- the new state is in the current term with a strictly higher version;
- it does not start a reconfiguration while one is pending;
- its join votes form a quorum of the new state's accepted configuration.

The result is a publish request carrying the state unchanged. The node records the new published version and configuration and clears its publish votes.
