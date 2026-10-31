# Read-back: `OpenSearchCoordination.init_javaInvariant`

## Notions used

**Coordination states.** For a payload type $V$, a coordination state $cs$ has nine fields:

- $\mathrm{localNode}$, a node with an id and an eligibility flag;
- $\mathrm{currentTerm} \in \mathbb{N}$;
- $\mathrm{lastAcceptedState}$, a cluster state;
- $\mathrm{joinVotes}$ and $\mathrm{publishVotes}$, vote collections (lists of ids);
- $\mathrm{startedJoinSinceLastReboot}$ and $\mathrm{electionWon}$, Booleans;
- $\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $\mathrm{lastPublishedConfiguration}$.

A cluster state $S$ has a term $S.\mathrm{term} \in \mathbb{N}$, a version $\in \mathbb{Z}$, last committed and last accepted voting configurations, and other independent fields. Abbreviations, all read from $cs.\mathrm{lastAcceptedState}$:

- $\mathrm{lat}(cs)$: its term;
- $\mathrm{lav}(cs)$: its version;
- $\mathrm{C}(cs)$ and $\mathrm{A}(cs)$: its two configurations.

**Constructor.** $\mathrm{init}(n, t, S)$ is the state with:

- $\mathrm{localNode} = n$;
- $\mathrm{currentTerm} = t$;
- $\mathrm{lastAcceptedState} = S$;
- $\mathrm{joinVotes} = \mathrm{publishVotes} = [\,]$;
- $\mathrm{startedJoinSinceLastReboot} = \mathrm{electionWon} = \mathrm{false}$;
- $\mathrm{lastPublishedVersion} = 0$;
- $\mathrm{lastPublishedConfiguration} = S.\mathrm{lastAcceptedConfiguration}$.

**Quorums.**

- $\mathrm{isQuorum}(v, c)$ holds iff $2\,|\{x \in c.\mathrm{nodeIds} : x \in v.\mathrm{nodes}\}| > |c.\mathrm{nodeIds}|$. It is false whenever $v$ is empty.
- An election strategy $es$ is an arbitrary Boolean function $f_{es}$.
- $\mathrm{isElectionQuorum}(es, cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{A}(cs)) \wedge f_{es}(cs.\mathrm{localNode}, cs.\mathrm{currentTerm}, \mathrm{lat}(cs), \mathrm{lav}(cs), \mathrm{C}(cs), \mathrm{A}(cs), v)$.

**The Java invariant.** $\mathrm{javaInvariant}(es, cs)$ is the conjunction of:

- (i) $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$;
- (ii) $cs.\mathrm{electionWon} = \mathrm{isElectionQuorum}(es, cs, cs.\mathrm{joinVotes})$;
- (iii) if $cs.\mathrm{electionWon}$, then $cs.\mathrm{lastPublishedVersion} \ge \mathrm{lav}(cs)$; otherwise $cs.\mathrm{lastPublishedVersion} = 0$;
- (iv) $cs.\mathrm{electionWon} \to cs.\mathrm{startedJoinSinceLastReboot}$;
- (v) $cs.\mathrm{publishVotes}$ is empty $\vee\ cs.\mathrm{electionWon}$.

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $es$: an election strategy;
- $n$: a node;
- $t \in \mathbb{N}$;
- $S$ (`s`): a cluster state over $V$.

**Hypothesis.** $h$: $S.\mathrm{term} \le t$.

**Conclusion.** $\mathrm{javaInvariant}(es, \mathrm{init}(n, t, S))$. Unfolded, it states the following:

- (i) $S.\mathrm{term} \le t$. This is the hypothesis itself.
- (ii) $\mathrm{false} = \mathrm{isElectionQuorum}(es, \mathrm{init}(n,t,S), [\,])$. The right side is false because the empty vote collection is not a quorum.
- (iii) Since the election is not won, $0 = 0$.
- (iv) This holds vacuously.
- (v) The publish votes are empty.

## 2. What is not constrained

- $es$ is arbitrary. No monotonicity is needed.
- $n$ is arbitrary.
- $S$ is arbitrary apart from $h$. Its configurations may be empty or non-empty, and its version, metadata version and other fields are free.
- $h$ is necessary: conjunct (i) for the initial state is exactly $h$.
- The hypothesis is satisfiable, for example with $t = S.\mathrm{term}$. The statement is not vacuous.
- The statement is about the constructor only. It says nothing about later steps.

## 3. Plain-language summary

A freshly constructed (restarted) coordination state satisfies all five Java invariant assertions, for every election strategy, provided the persisted accepted term does not exceed the persisted current term.
