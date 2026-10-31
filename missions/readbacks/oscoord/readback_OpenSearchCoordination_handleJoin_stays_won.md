# Read-back: `OpenSearchCoordination.handleJoin_stays_won`

## Notions used

**Coordination states.** A coordination state $cs$ has nine fields: localNode (a node), currentTerm, lastAcceptedState, joinVotes (a vote collection, i.e. a list of ids), startedJoinSinceLastReboot, electionWon (a Boolean), lastPublishedVersion, lastPublishedConfiguration and publishVotes. Abbreviations, all read from the last accepted state:

- $\mathrm{lat}(cs)$: its term;
- $\mathrm{lav}(cs)$: its version;
- $\mathrm{lavm}(cs)$: its metadata version if the term is $0$, otherwise its version;
- $\mathrm{C}(cs)$, $\mathrm{A}(cs)$: its last committed and last accepted voting configurations.

**Quorums and votes.**

- $\mathrm{isQuorum}(v, c)$ holds iff strictly more than half of the ids of configuration $c$ occur in $v.\mathrm{nodes}$.
- $\mathrm{addVote}(v, n)$ prepends $n.\mathrm{id}$ when $n$ is eligible and not yet present. Otherwise it leaves $v$ unchanged. In either case it also returns whether it added.

**Election strategy, election quorum, monotonicity.** A strategy $es$ is an arbitrary Boolean function $f_{es}$ of a node, two naturals, an integer, two configurations and a vote collection.
$$\mathrm{isElectionQuorum}(es, cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{A}(cs)) \wedge f_{es}(cs.\mathrm{localNode}, cs.\mathrm{currentTerm}, \mathrm{lat}(cs), \mathrm{lav}(cs), \mathrm{C}(cs), \mathrm{A}(cs), v).$$
$\mathrm{Monotone}(es)$ means: for all fixed values of the first six arguments, if every id of $v$ is in $w$ and $f_{es}(\dots, v) = \mathrm{true}$, then $f_{es}(\dots, w) = \mathrm{true}$.

**The handler** $\mathrm{handleJoin}(es, cs, j)$ has two cases.

- **Guards.** It fails unless all of the following hold:
  - $j.\mathrm{term} = cs.\mathrm{currentTerm}$;
  - $cs.\mathrm{startedJoinSinceLastReboot}$ holds;
  - $j$'s last-accepted term and version are not ahead of $(\mathrm{lat}(cs), \mathrm{lavm}(cs))$;
  - $\mathrm{A}(cs)$ is non-empty.
- **Success.** Otherwise, with $v' = \mathrm{addVote}(cs.\mathrm{joinVotes}, j.\mathrm{sourceNode}).1$, the result $cs'$ has:
  - $\mathrm{joinVotes} = v'$;
  - $\mathrm{electionWon} = \mathrm{isElectionQuorum}(es, cs, v')$;
  - $\mathrm{lastPublishedVersion} := \mathrm{lav}(cs)$ if the election is newly won.

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $es$: an election strategy;
- $cs$: a coordination state;
- $j$: a join;
- $cs'$: a coordination state;
- $b$: a Boolean.

**Hypotheses, in order.**
1. $\mathit{hes}$: $\mathrm{Monotone}(es)$;
2. $\mathit{hinv}$: $cs.\mathrm{electionWon} = \mathrm{isElectionQuorum}(es, cs, cs.\mathrm{joinVotes})$. This is conjunct (ii) of the Java invariant, an equality of Booleans.
3. $h$: $\mathrm{handleJoin}(es, cs, j) = \mathrm{ok}(cs', b)$;
4. $\mathit{hw}$: $cs.\mathrm{electionWon} = \mathrm{true}$.

**Conclusion.** $cs'.\mathrm{electionWon} = \mathrm{true}$.

Combined, $\mathit{hinv}$ and $\mathit{hw}$ say that the node's current join votes form an election quorum. The conclusion says that after any successful join, the recomputed flag is still $\mathrm{true}$.

## 2. What is not constrained

- **The strategy must be monotone.** For a non-monotone strategy nothing is claimed. Such a strategy could make a successful join lower the flag; this is the Java assertion at CoordinationState.java:323.
- **Only one invariant conjunct is assumed.** $\mathit{hinv}$ is conjunct (ii) of `javaInvariant` alone. The others (term bound, published-version condition, startedJoin, publish votes) are not assumed. Nothing in the statement needs them.
- **$j$ is arbitrary apart from $h$.** That includes a join from an ineligible or already-counted node, which leaves the votes unchanged.
- **Only the flag is claimed.** Nothing is said about $b$, the votes or the published version.
- **The hypotheses are jointly satisfiable**, so the statement is not vacuous. For example, take the default strategy, a node with id $0$ whose committed and accepted configurations are both $[0]$, joinVotes $[0]$, $\mathrm{electionWon} = \mathrm{true}$, $\mathrm{startedJoinSinceLastReboot} = \mathrm{true}$, and a join in the current term whose last-accepted term is lower.

## 3. Plain-language summary

Under a monotone election strategy, a node that has won its election, with the stored won flag agreeing with the quorum test on its current votes, still has its election won after any successful join. In words, "won cannot become not-won".
