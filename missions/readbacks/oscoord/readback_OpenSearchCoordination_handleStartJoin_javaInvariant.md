# Read-back: `OpenSearchCoordination.handleStartJoin_javaInvariant`

## Notions used

**Coordination states.** A coordination state $cs$ has nine fields:

- $\mathrm{localNode}$;
- $\mathrm{currentTerm} \in \mathbb{N}$;
- $\mathrm{lastAcceptedState}$, a cluster state with a term, a version, last committed and last accepted configurations, and other fields;
- $\mathrm{joinVotes}$ and $\mathrm{publishVotes}$, vote collections (lists of ids);
- $\mathrm{startedJoinSinceLastReboot}$ and $\mathrm{electionWon}$;
- $\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $\mathrm{lastPublishedConfiguration}$.

Abbreviations, all read from the accepted state:

- $\mathrm{lat}(cs)$: its term;
- $\mathrm{lav}(cs)$: its version;
- $\mathrm{lavm}(cs)$: its metadata version if the term is $0$, otherwise its version;
- $\mathrm{C}(cs)$ and $\mathrm{A}(cs)$: its two configurations.

**Quorums.**

- $\mathrm{isQuorum}(v, c)$ is the strict-majority test. It is false whenever $v$ is empty.
- An election strategy $es$ is an arbitrary Boolean function $f_{es}$.
- $\mathrm{isElectionQuorum}(es, cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{A}(cs)) \wedge f_{es}(\dots, v)$.

**The Java invariant.** $\mathrm{javaInvariant}(es, cs)$ is the conjunction of:

- (i) $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$;
- (ii) $cs.\mathrm{electionWon} = \mathrm{isElectionQuorum}(es, cs, cs.\mathrm{joinVotes})$;
- (iii) if $cs.\mathrm{electionWon}$, then $cs.\mathrm{lastPublishedVersion} \ge \mathrm{lav}(cs)$; otherwise $cs.\mathrm{lastPublishedVersion} = 0$;
- (iv) $cs.\mathrm{electionWon} \to cs.\mathrm{startedJoinSinceLastReboot}$;
- (v) $cs.\mathrm{publishVotes}$ is empty $\vee\ cs.\mathrm{electionWon}$.

**The handler.** $\mathrm{handleStartJoin}(cs, r)$ fails if $r.\mathrm{term} \le cs.\mathrm{currentTerm}$. Otherwise it returns $cs$ updated as follows:

- $\mathrm{currentTerm} := r.\mathrm{term}$;
- $\mathrm{lastPublishedVersion} := 0$;
- $\mathrm{lastPublishedConfiguration} := \mathrm{A}(cs)$;
- $\mathrm{startedJoinSinceLastReboot} := \mathrm{true}$;
- $\mathrm{electionWon} := \mathrm{false}$;
- $\mathrm{joinVotes} := [\,]$ and $\mathrm{publishVotes} := [\,]$.

The accepted state and the local node are unchanged. The handler also returns a join.

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $es$: an election strategy;
- $cs$: a coordination state;
- $r$: a start-join request;
- $cs'$: a coordination state;
- $j$: a join.

**Hypotheses, in order.**
1. $\mathit{hcs}$: $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$;
2. $h$: $\mathrm{handleStartJoin}(cs, r) = \mathrm{ok}(cs', j)$.

**Conclusion.** $\mathrm{javaInvariant}(es, cs')$. Unfolded with the handler's result:

- (i) $\mathrm{lat}(cs) \le r.\mathrm{term}$. This follows from $\mathit{hcs}$ and $r.\mathrm{term} > cs.\mathrm{currentTerm}$.
- (ii) $\mathrm{false} = \mathrm{isElectionQuorum}(es, cs', [\,])$. The right side is false.
- (iii) $0 = 0$.
- (iv) This holds vacuously.
- (v) The publish votes are empty.

## 2. What is not constrained

- **$cs$ need not satisfy the Java invariant.** Only conjunct (i) is assumed, as $\mathit{hcs}$. The other four conjuncts are re-established by the reset, whatever $cs$'s votes, flags and published version were.
- **$es$ is arbitrary.** No monotonicity is needed.
- **$r$ and $j$ are constrained only through $h$.** The request's source node is arbitrary.
- **Not vacuous.** The hypotheses are satisfiable: any $cs$ with $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$ and any $r$ with a larger term work.

## 3. Plain-language summary

A successful start-join, applied to any state whose last-accepted term is at most its current term, produces a state that satisfies all five Java invariant assertions, for every election strategy. This works because start-join clears the votes, resets the won flag and published version, and moves to a strictly larger term.
