# Read-back: `OpenSearchCoordination.javaInvariant_not_local`

## Notions used

**Coordination states over `Unit`.** In this statement the payload type is `Unit`, so the cluster states' "everything else" field carries no information. A coordination state $cs$ has nine fields:

- $\mathrm{localNode}$;
- $\mathrm{currentTerm} \in \mathbb{N}$;
- $\mathrm{lastAcceptedState}$, a cluster state with a term, a version, a metadata version, last committed and last accepted configurations, an optional cluster-manager id, two UUID flags and the unit payload;
- $\mathrm{joinVotes}$ and $\mathrm{publishVotes}$;
- $\mathrm{startedJoinSinceLastReboot}$ and $\mathrm{electionWon}$;
- $\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $\mathrm{lastPublishedConfiguration}$.

Abbreviations, all read from the accepted state:

- $\mathrm{lat}(cs)$: its term;
- $\mathrm{lav}(cs)$: its version;
- $\mathrm{C}(cs)$ and $\mathrm{A}(cs)$: its configurations.

**Default election quorum.** $\mathrm{DEFAULT\_INSTANCE}$ is the strategy whose extra constraint is always true. Hence
$$\mathrm{isElectionQuorum}(\mathrm{DEFAULT}, cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{A}(cs)),$$
where $\mathrm{isQuorum}(v, c)$ holds iff strictly more than half of $c$'s ids occur in $v$.

**The Java invariant.** $\mathrm{javaInvariant}(es, cs)$ is the conjunction of:

- (i) $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$;
- (ii) $cs.\mathrm{electionWon} = \mathrm{isElectionQuorum}(es, cs, cs.\mathrm{joinVotes})$;
- (iii) if $cs.\mathrm{electionWon}$, then $cs.\mathrm{lastPublishedVersion} \ge \mathrm{lav}(cs)$; otherwise $cs.\mathrm{lastPublishedVersion} = 0$;
- (iv) $cs.\mathrm{electionWon} \to cs.\mathrm{startedJoinSinceLastReboot}$;
- (v) $cs.\mathrm{publishVotes}$ is empty $\vee\ cs.\mathrm{electionWon}$.

**The handler.** $\mathrm{handlePublishRequest}(cs, R)$, with $S = R.\mathrm{acceptedState}$, works as follows:

1. It fails if $S.\mathrm{term} \ne cs.\mathrm{currentTerm}$.
2. Otherwise, if $S.\mathrm{term} = \mathrm{lat}(cs)$ and $S.\mathrm{version} \le \mathrm{lav}(cs)$, it fails, except in the term-0 compatibility case. There it accepts iff $S$ names a cluster manager $\mathrm{some}\ m$ different from the stored one.
3. In every other case it accepts.

Accepting returns $\mathrm{ok}(cs \text{ with } \mathrm{lastAcceptedState} := S,\ \langle S.\mathrm{term}, S.\mathrm{version}\rangle)$.

## 1. Declaration

**Binders and hypotheses.** None.

**Conclusion.** An existential:
$$\exists\, cs\ R\ cs'\ r,\quad \mathrm{javaInvariant}(\mathrm{DEFAULT}, cs) \;\wedge\; \mathrm{handlePublishRequest}(cs, R) = \mathrm{ok}(cs', r) \;\wedge\; \neg\,\mathrm{javaInvariant}(\mathrm{DEFAULT}, cs'),$$
where $cs, cs'$ are coordination states over `Unit`, $R$ is a publish request over `Unit`, and $r$ is a publish response. There is a state satisfying the Java invariant under the default strategy which accepts some publish request and thereby reaches a state violating the invariant.

**Which conjuncts a witness can break.** A successful `handlePublishRequest` replaces only the accepted state, by one whose term equals $cs.\mathrm{currentTerm}$. So conjuncts (i), (iv) and (v) automatically hold after the step. A witness must break (ii) or (iii):

- (ii) breaks when the new accepted configurations change the quorum test.
- (iii) breaks when the election is won and the new accepted version exceeds $\mathrm{lastPublishedVersion}$.

**A witness.** I checked this one by evaluating the definitions. Let $cs$ be:

- local node $\langle 0, \mathrm{eligible}\rangle$, current term $1$;
- accepted state of term $1$ and version $0$, with both configurations $\{0\}$;
- join votes $[0]$, $\mathrm{startedJoinSinceLastReboot} = \mathrm{electionWon} = \mathrm{true}$;
- published version $0$ and no publish votes.

This $cs$ satisfies (i)–(v). Now take $S$ equal to its accepted state but with version $5$. The request is accepted, because $S.\mathrm{term} = 1$ and $5 > 0$. The result has $\mathrm{electionWon} = \mathrm{true}$ but $\mathrm{lastPublishedVersion} = 0 < 5 = \mathrm{lav}(cs')$, so (iii) fails.

## 2. What is not constrained

- **A pure existence claim.** It fixes the payload type `Unit` and the default strategy. It does not characterize which states or requests break the invariant.
- **Nothing about reachability.** It does not say that such a state and request can occur in a run of a cluster: no reachability or cluster model is involved. The state $cs$ need only satisfy the five local conjuncts.
- **Not vacuous.** It is a satisfiable existential (witness above).
- **A statement about scope.** Its content is a limitation of local reasoning: `javaInvariant` is not an invariant of the single-node handler `handlePublishRequest`. This explains why `javaInvariant_preserved` omits that handler. It does not imply that the other omitted handlers preserve the invariant; for `handleCommit` they do not (see the read-back of `javaInvariant_preserved`).

## 3. Plain-language summary

The five Java invariant assertions are not preserved by `handlePublishRequest` taken alone. Some state satisfies them under the default strategy, accepts a publish request, and ends up violating them. For example, an election winner whose last published version is $0$ accepts a newer version of its own term from a publish request, so its published version falls behind its accepted version.
