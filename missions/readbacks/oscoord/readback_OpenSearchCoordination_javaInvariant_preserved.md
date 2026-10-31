# Read-back: `OpenSearchCoordination.javaInvariant_preserved`

## Notions used

**Coordination states.** For a payload type $V$, a coordination state $cs$ has nine fields:

- $\mathrm{localNode}$, a node with an id and an eligibility flag;
- $\mathrm{currentTerm} \in \mathbb{N}$;
- $\mathrm{lastAcceptedState}$, a cluster state with a term, version, metadata version, last committed and last accepted voting configurations, and other fields;
- $\mathrm{joinVotes}$ and $\mathrm{publishVotes}$, vote collections (lists of ids);
- $\mathrm{startedJoinSinceLastReboot}$ and $\mathrm{electionWon}$;
- $\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $\mathrm{lastPublishedConfiguration}$.

Abbreviations, all read from the accepted state:

- $\mathrm{lat}(cs)$: its term;
- $\mathrm{lav}(cs)$: its version;
- $\mathrm{lavm}(cs)$: its metadata version if the term is $0$, otherwise its version;
- $\mathrm{C}(cs)$ and $\mathrm{A}(cs)$: its last committed and last accepted configurations.

**Quorums, votes, strategies.**

- $\mathrm{isQuorum}(v, c)$ holds iff strictly more than half of $c$'s ids occur in $v$.
- $\mathrm{addVote}(v, n)$ prepends $n.\mathrm{id}$ if $n$ is eligible and absent. Otherwise it leaves $v$ unchanged.
- An election strategy $es$ is an arbitrary Boolean function $f_{es}$.
- $\mathrm{isElectionQuorum}(es, cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{A}(cs)) \wedge f_{es}(cs.\mathrm{localNode}, cs.\mathrm{currentTerm}, \mathrm{lat}(cs), \mathrm{lav}(cs), \mathrm{C}(cs), \mathrm{A}(cs), v)$.
- $\mathrm{Monotone}(es)$: with the first six arguments fixed, if $f_{es}$ holds for $v$ and every id of $v$ is in $w$, then $f_{es}$ holds for $w$.

**The Java invariant.** $\mathrm{javaInvariant}(es, cs)$ is the conjunction of:

- (i) $\mathrm{lat}(cs) \le cs.\mathrm{currentTerm}$;
- (ii) $cs.\mathrm{electionWon} = \mathrm{isElectionQuorum}(es, cs, cs.\mathrm{joinVotes})$;
- (iii) if $cs.\mathrm{electionWon}$, then $cs.\mathrm{lastPublishedVersion} \ge \mathrm{lav}(cs)$; otherwise $cs.\mathrm{lastPublishedVersion} = 0$;
- (iv) $cs.\mathrm{electionWon} \to cs.\mathrm{startedJoinSinceLastReboot}$;
- (v) $cs.\mathrm{publishVotes}$ is empty $\vee\ cs.\mathrm{electionWon}$.

**The three handlers.**

- **$\mathrm{handleJoin}(es, cs, j)$.**
  - *Guards:* $j.\mathrm{term} = cs.\mathrm{currentTerm}$; $cs.\mathrm{startedJoinSinceLastReboot}$; $j$'s accepted term and version are not ahead of $(\mathrm{lat}, \mathrm{lavm})$; $\mathrm{A}(cs)$ is non-empty.
  - *Effect:* $\mathrm{joinVotes}$ becomes $v' = \mathrm{addVote}(cs.\mathrm{joinVotes}, j.\mathrm{sourceNode}).1$, and $\mathrm{electionWon}$ becomes $\mathrm{isElectionQuorum}(es, cs, v')$. If the election is newly won, $\mathrm{lastPublishedVersion}$ becomes $\mathrm{lav}(cs)$. Nothing else changes.
- **$\mathrm{handleClientValue}(cs, S)$.**
  - *Guards:* the election is won; $cs.\mathrm{lastPublishedVersion} = \mathrm{lav}(cs)$; $S.\mathrm{term} = cs.\mathrm{currentTerm}$; $S.\mathrm{version} > cs.\mathrm{lastPublishedVersion}$; no reconfiguration while reconfiguring; the join votes form a quorum of $S$'s accepted configuration.
  - *Effect:* $\mathrm{lastPublishedVersion} := S.\mathrm{version}$, $\mathrm{lastPublishedConfiguration} := S.\mathrm{lastAcceptedConfiguration}$, $\mathrm{publishVotes} := [\,]$.
- **$\mathrm{handlePublishResponse}(cs, n, r)$.**
  - *Guards:* the election is won; $r.\mathrm{term} = cs.\mathrm{currentTerm}$; $r.\mathrm{version} = cs.\mathrm{lastPublishedVersion}$.
  - *Effect:* $\mathrm{publishVotes}$ becomes $\mathrm{addVote}(cs.\mathrm{publishVotes}, n).1$.

None of the three changes $\mathrm{localNode}$, $\mathrm{currentTerm}$ or $\mathrm{lastAcceptedState}$. Those are the only fields, besides the votes argument, that $\mathrm{isElectionQuorum}$ reads.

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $es$: an election strategy;
- $cs$: a coordination state.

**Hypotheses, in order.**
1. $\mathit{hes}$: $\mathrm{Monotone}(es)$;
2. $\mathit{hinv}$: $\mathrm{javaInvariant}(es, cs)$.

**Conclusion.** The conjunction of three clauses:

1. $\forall j\ cs'\ b,\ \mathrm{handleJoin}(es, cs, j) = \mathrm{ok}(cs', b) \to \mathrm{javaInvariant}(es, cs')$;
2. $\forall S\ cs'\ p,\ \mathrm{handleClientValue}(cs, S) = \mathrm{ok}(cs', p) \to \mathrm{javaInvariant}(es, cs')$;
3. $\forall n\ r\ cs'\ o,\ \mathrm{handlePublishResponse}(cs, n, r) = \mathrm{ok}(cs', o) \to \mathrm{javaInvariant}(es, cs')$.

In words: from a state satisfying all five Java invariant conjuncts under a monotone strategy, one successful step of any of these three handlers leads to a state satisfying them again, for the same strategy.

## 2. What is not constrained

- **Scope: three of the seven handlers.**
  - `handleStartJoin` is covered separately by `handleStartJoin_javaInvariant`, under the weaker hypothesis of conjunct (i) only.
  - `handlePublishRequest` is shown *not* to preserve the invariant by `javaInvariant_not_local`.
  - `setInitialState` and `handleCommit` are covered by **no** theorem of the mission.
- **Observation about `handleCommit`.** This is not a claim of any theorem; I checked it by evaluating the definitions. `handleCommit` does not preserve `javaInvariant` even under `DEFAULT_INSTANCE`. Take node 4 with:
  - current term $1$, accepted state of term $1$ and version $3$;
  - committed configuration $\{1,2,3\}$ and accepted configuration $\{4\}$;
  - join votes $[4]$, $\mathrm{electionWon} = \mathrm{false}$, $\mathrm{startedJoinSinceLastReboot} = \mathrm{true}$, published version $0$, no publish votes.

  This state satisfies all five conjuncts: the votes are not a quorum of $\{1,2,3\}$. Now apply the commit $\langle\_, 1, 3\rangle$. It succeeds and sets the committed configuration to $\{4\}$. The quorum test becomes true while $\mathrm{electionWon}$ stays false, which breaks (ii). So this theorem together with `javaInvariant_not_local` should not be read as saying that publish requests are the only steps that break the invariant.
- **Monotonicity is assumed for all three clauses.** Only the join clause needs it, to rule out a won election becoming not won, since conjuncts (iii) and (v) depend on that. The other two clauses do not change the votes or the flag.
- **The same strategy throughout.** $es$ is the strategy both in the invariant and in `handleJoin`.
- **One step at a time.** Each clause is a single-step implication from success. The statement says nothing about sequences of steps that interleave other handlers.
- **Not vacuous.** The hypotheses are satisfiable: for example, `init` of any state with accepted term $\le$ current term satisfies `javaInvariant`, and the default strategy is monotone.

## 3. Plain-language summary

Under a monotone election strategy, if a coordination state satisfies the five assertions of Java's `invariant()`, then any successful join, client-value or publish-response step yields a state that satisfies them again. The theorem says nothing about publish requests, commits or initial-state injection.
