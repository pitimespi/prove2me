# Read-back: `OpenSearchCoordination.lastAcceptedTerm_le_currentTerm`

## Notions used

**Coordination states.** A coordination state $cs$ over a payload type $V$ has nine fields:

- localNode;
- $\mathrm{currentTerm} \in \mathbb{N}$;
- lastAcceptedState, a cluster state with a term $\in \mathbb{N}$, a version $\in \mathbb{Z}$, two voting configurations, and further fields;
- joinVotes;
- startedJoinSinceLastReboot;
- electionWon;
- lastPublishedVersion;
- lastPublishedConfiguration;
- publishVotes.

Abbreviations:

- $\mathrm{lat}(cs) = cs.\mathrm{lastAcceptedState}.\mathrm{term}$;
- $\mathrm{lav}(cs) = cs.\mathrm{lastAcceptedState}.\mathrm{version}$;
- $\mathrm{A}(cs)$ = the accepted state's last accepted configuration.

**The seven handlers.** Here is what each one does to $\mathrm{currentTerm}$ and $\mathrm{lastAcceptedState}$ when it returns $\mathrm{ok}$; their other effects do not matter for this statement.

- $\mathrm{setInitialState}(cs, S)$ succeeds iff $\mathrm{A}(cs)$ is empty. The result is $cs$ with $\mathrm{lastAcceptedState} := S$. Nothing about $S$ is checked, in particular not $S.\mathrm{term}$.
- $\mathrm{handleStartJoin}(cs, r)$ succeeds iff $r.\mathrm{term} > cs.\mathrm{currentTerm}$. The result's $\mathrm{currentTerm}$ is $r.\mathrm{term}$, and $\mathrm{lastAcceptedState}$ is unchanged. A join is also returned.
- $\mathrm{handleJoin}(es, cs, j)$ leaves both fields unchanged. It changes only votes, the won flag and the published version. A Boolean is also returned.
- $\mathrm{handleClientValue}(cs, S)$ leaves both fields unchanged. It changes the published version and configuration and the publish votes. A publish request is also returned.
- $\mathrm{handlePublishRequest}(cs, R)$ succeeds only if $R.\mathrm{acceptedState}.\mathrm{term} = cs.\mathrm{currentTerm}$. The result is $cs$ with $\mathrm{lastAcceptedState} := R.\mathrm{acceptedState}$. A publish response is also returned.
- $\mathrm{handlePublishResponse}(cs, n, r)$ leaves both fields unchanged. It changes only the publish votes. An optional commit request is also returned.
- $\mathrm{handleCommit}(cs, c)$ replaces $\mathrm{lastAcceptedState}$ by $\mathrm{markCommitted}$ of it. That operation changes only the committed configuration and a UUID flag; the term is unchanged. $\mathrm{currentTerm}$ is also unchanged.

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $es$: an election strategy, an arbitrary Boolean function used inside `handleJoin`;
- $cs$: a coordination state.

**Hypothesis.** $\mathit{hcs}$: $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$.

**Conclusion.** A conjunction of seven clauses, one per handler:

1. $\forall S\ cs',\ \mathrm{setInitialState}(cs, S) = \mathrm{ok}(cs') \to S.\mathrm{term} = 0 \to \mathrm{lat}(cs') \le cs'.\mathrm{currentTerm} \wedge cs'.\mathrm{currentTerm} = cs.\mathrm{currentTerm}$.
2. $\forall r\ cs'\ j,\ \mathrm{handleStartJoin}(cs, r) = \mathrm{ok}(cs', j) \to \mathrm{lat}(cs') \le cs'.\mathrm{currentTerm} \wedge cs.\mathrm{currentTerm} < cs'.\mathrm{currentTerm}$.
3. $\forall j\ cs'\ b,\ \mathrm{handleJoin}(es, cs, j) = \mathrm{ok}(cs', b) \to \mathrm{lat}(cs') \le cs'.\mathrm{currentTerm} \wedge cs'.\mathrm{currentTerm} = cs.\mathrm{currentTerm}$.
4. $\forall S\ cs'\ p,\ \mathrm{handleClientValue}(cs, S) = \mathrm{ok}(cs', p) \to$ (the same two facts as in 3).
5. $\forall R\ cs'\ r,\ \mathrm{handlePublishRequest}(cs, R) = \mathrm{ok}(cs', r) \to$ (the same).
6. $\forall n\ r\ cs'\ o,\ \mathrm{handlePublishResponse}(cs, n, r) = \mathrm{ok}(cs', o) \to$ (the same).
7. $\forall c\ cs',\ \mathrm{handleCommit}(cs, c) = \mathrm{ok}(cs') \to$ (the same).

Each clause says two things:

- One successful step of that handler from $cs$ yields a state $cs'$ whose last-accepted term is at most its current term.
- The current term strictly increases (clause 2) or is unchanged (all other clauses).

## 2. What is not constrained

- **Clause 1 has its own extra hypothesis, $S.\mathrm{term} = 0$.** This is the only part of Java's `setInitialState` assertions (`initialStateContract`) that is used. `setInitialState` does not check it, so without it the clause could fail: $S.\mathrm{term} > cs.\mathrm{currentTerm}$ would be accepted. Clause 1 does not need $\mathit{hcs}$.
- **This is one-step preservation, not an invariant.** The name suggests an invariant, but the content is preservation by a single step from any state satisfying $\mathit{hcs}$.
  - The statement does not mention `init`. Separately, `init(n, t, S)` satisfies the inequality only when $S.\mathrm{term} \le t$.
  - It says nothing about sequences of steps or reachability.
- **$es$ matters only for clause 3.**
- **Clause 5 claims less than holds.** It states only $\le$, but in fact $\mathrm{lat}(cs') = cs.\mathrm{currentTerm}$.
- **No other fields are mentioned.**
- **Each clause's antecedent is satisfiable,** so the statement is not vacuous. If a handler fails on some input, that clause is vacuous for that input.

## 3. Plain-language summary

Starting from any coordination state whose last-accepted term is at most its current term, each of the seven handlers, when it succeeds, produces a state with the same property. `handleStartJoin` strictly increases the current term, and every other handler leaves it unchanged. For `setInitialState` this is claimed only for initial states of term $0$.
