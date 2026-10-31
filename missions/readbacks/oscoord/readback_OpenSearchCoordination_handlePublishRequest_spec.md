# Read-back: `OpenSearchCoordination.handlePublishRequest_spec`

## Notions used

**Coordination states and cluster states.** For a payload type $V$, a coordination state $cs$ has nine fields:

- $cs.\mathrm{localNode}$: a node;
- $cs.\mathrm{currentTerm} \in \mathbb{N}$;
- $cs.\mathrm{lastAcceptedState}$: a cluster state;
- $cs.\mathrm{joinVotes}$ and $cs.\mathrm{publishVotes}$: vote collections;
- $cs.\mathrm{startedJoinSinceLastReboot}$ and $cs.\mathrm{electionWon}$: Booleans;
- $cs.\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $cs.\mathrm{lastPublishedConfiguration}$: a voting configuration.

A cluster state $S$ has nine independent fields:

- $S.\mathrm{term} \in \mathbb{N}$;
- $S.\mathrm{version} \in \mathbb{Z}$ and $S.\mathrm{metadataVersion} \in \mathbb{Z}$;
- two voting configurations, $S.\mathrm{lastCommittedConfiguration}$ and $S.\mathrm{lastAcceptedConfiguration}$;
- $S.\mathrm{clusterManagerNode}$, an optional natural (an ephemeral id);
- two Booleans about the cluster UUID;
- a payload $S.\mathrm{value} \in V$.

Abbreviations:

- $\mathrm{lat}(cs) = cs.\mathrm{lastAcceptedState}.\mathrm{term}$ (`lastAcceptedTerm`);
- $\mathrm{lav}(cs) = cs.\mathrm{lastAcceptedState}.\mathrm{version}$ (`lastAcceptedVersion`).

$\mathrm{ZEN1\_BWC\_TERM} = 0$.

**Messages.** A publish request $R$ carries one cluster state $R.\mathrm{acceptedState}$. A publish response is a pair $\langle \mathrm{term} \in \mathbb{N}, \mathrm{version} \in \mathbb{Z}\rangle$.

**The handler** $\mathrm{handlePublishRequest}(cs, R)$, with $S = R.\mathrm{acceptedState}$. Let $\mathit{accept} = \mathrm{ok}(cs \text{ with } \mathrm{lastAcceptedState} := S,\ \langle S.\mathrm{term}, S.\mathrm{version}\rangle)$. The handler proceeds as follows:

1. If $S.\mathrm{term} \ne cs.\mathrm{currentTerm}$, it returns $\mathrm{error}$.
2. Else, if $S.\mathrm{term} = \mathrm{lat}(cs)$ and $S.\mathrm{version} \le \mathrm{lav}(cs)$:
   - if $S.\mathrm{term} = 0$:
     - if $S.\mathrm{clusterManagerNode} = \mathrm{none}$, it returns $\mathrm{error}$;
     - if $S.\mathrm{clusterManagerNode} = \mathrm{some}\ m$, it returns $\mathit{accept}$ when $\mathrm{some}\ m \ne cs.\mathrm{lastAcceptedState}.\mathrm{clusterManagerNode}$, and $\mathrm{error}$ otherwise;
   - otherwise, it returns $\mathrm{error}$.
3. Else, it returns $\mathit{accept}$.

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $cs$: a coordination state;
- $R$ (`req`): a publish request;
- $cs'$: a coordination state;
- $\mathit{resp}$: a publish response.

Write $S = R.\mathrm{acceptedState}$.

**Hypotheses, in order.**
1. $\mathit{hcs}$: $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$;
2. $h$: $\mathrm{handlePublishRequest}(cs, R) = \mathrm{ok}(cs', \mathit{resp})$.

**Conclusion.** The conjunction of:

1. $cs'.\mathrm{lastAcceptedState} = S$;
2. $S.\mathrm{term} = cs.\mathrm{currentTerm}$;
3. $cs'.\mathrm{currentTerm} = cs.\mathrm{currentTerm}$;
4. $cs'.\mathrm{localNode} = cs.\mathrm{localNode}$;
5. $\mathit{resp} = \langle S.\mathrm{term}, S.\mathrm{version}\rangle$;
6. $\mathrm{lat}(cs) < S.\mathrm{term}\ \ \vee\ \ \big(\mathrm{lat}(cs) = S.\mathrm{term} \wedge \mathrm{lav}(cs) < S.\mathrm{version}\big)\ \ \vee\ \ S.\mathrm{term} = \mathrm{ZEN1\_BWC\_TERM}\ (=0)$;
7. $cs'.\mathrm{joinVotes} = cs.\mathrm{joinVotes}$;
8. $cs'.\mathrm{electionWon} = cs.\mathrm{electionWon}$;
9. $cs'.\mathrm{startedJoinSinceLastReboot} = cs.\mathrm{startedJoinSinceLastReboot}$;
10. $cs'.\mathrm{lastPublishedVersion} = cs.\mathrm{lastPublishedVersion}$;
11. $cs'.\mathrm{lastPublishedConfiguration} = cs.\mathrm{lastPublishedConfiguration}$;
12. $cs'.\mathrm{publishVotes} = cs.\mathrm{publishVotes}$.

Conjuncts 1, 3, 4 and 7–12 fix all nine fields of $cs'$: the accepted state is replaced by $S$ and nothing else changes. Conjunct 5 fixes the response.

## 2. What is not constrained

- **Only one direction.** The statement is an implication from success. It does not say that requests satisfying conjuncts 2 and 6 are accepted.
- **Conjunct 6 is weaker than the handler's real acceptance condition.** Its third alternative, $S.\mathrm{term} = 0$, holds for every term-0 request. So for term-0 requests conjunct 6 constrains nothing.
  - It omits the Zen1-branch condition: an incoming cluster manager $\mathrm{some}\ m$ that differs from the stored one.
  - It allows a term-0 state with a version lower than or equal to the current one.
- **The role of $\mathit{hcs}$.** $\mathit{hcs}$ is what makes conjunct 6 hold.
  - Without it, a state with $\mathrm{lat}(cs) > cs.\mathrm{currentTerm}$ would accept a request with $S.\mathrm{term} = cs.\mathrm{currentTerm} < \mathrm{lat}(cs)$ and $S.\mathrm{term} \ne 0$. That request satisfies none of the three alternatives.
  - Given $\mathit{hcs}$ and conjunct 2, the first alternative is equivalent to $S.\mathrm{term} \ne \mathrm{lat}(cs)$.
  - $\mathit{hcs}$ is satisfiable, so the statement is not vacuous. For example, any state with $\mathrm{lat}(cs) < cs.\mathrm{currentTerm}$ accepts any $S$ with $S.\mathrm{term} = cs.\mathrm{currentTerm}$.
- **The rest of $S$ is unconstrained.** Its configurations (including the committed one), $\mathrm{metadataVersion}$, $\mathrm{clusterManagerNode}$, UUID flags and payload are free. Accepting a publish may therefore replace the configurations arbitrarily.
- **$\mathrm{electionWon}$ is carried over unchanged** (conjunct 8). The election-quorum test depends on the accepted state's configurations, version and term, so the stored flag may stop matching that test. See `javaInvariant_not_local`.
- $cs$'s other fields are unconstrained. Only $\mathit{hcs}$ is assumed.

## 3. Plain-language summary

Suppose a node whose last-accepted term does not exceed its current term accepts a publish request. Then:

- the published state is in the node's current term and becomes its new last-accepted state;
- nothing else in the node changes;
- the response echoes that state's term and version;
- the accepted state is strictly newer than the old one in (term, version) order, except when its term is $0$ (Zen1 compatibility), where nothing is claimed.
