# Read-back: `OpenSearchCoordination.handleJoin_spec`

## Notions used

**Coordination states.** For a payload type $V$, a coordination state $cs$ has nine fields:

- $cs.\mathrm{localNode}$: a node, made of an id in $\mathbb{N}$ and a Boolean "eligible" flag;
- $cs.\mathrm{currentTerm} \in \mathbb{N}$;
- $cs.\mathrm{lastAcceptedState}$: a cluster state with a term $\in \mathbb{N}$, a version $\in \mathbb{Z}$, a metadata version $\in \mathbb{Z}$, last committed and last accepted voting configurations, and further fields;
- $cs.\mathrm{joinVotes}$ and $cs.\mathrm{publishVotes}$: vote collections, which are lists of ids;
- $cs.\mathrm{startedJoinSinceLastReboot}$ and $cs.\mathrm{electionWon}$: Booleans;
- $cs.\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $cs.\mathrm{lastPublishedConfiguration}$.

Abbreviations, all read from $cs.\mathrm{lastAcceptedState}$:

- $\mathrm{lat}(cs)$ = its term;
- $\mathrm{lav}(cs)$ = its version;
- $\mathrm{lavm}(cs)$ = its metadata version if its term is $0$, and its version otherwise;
- $\mathrm{C}(cs)$ = its last committed configuration;
- $\mathrm{A}(cs)$ = its last accepted configuration.

**Configurations and votes.**

- A voting configuration is a strictly increasing list of ids. $\mathrm{isEmpty}$ means the list is $[\,]$.
- $\mathrm{isQuorum}(v, c)$ holds iff $2\,|\{x \in c.\mathrm{nodeIds} : x \in v.\mathrm{nodes}\}| > |c.\mathrm{nodeIds}|$.
- $\mathrm{addVote}(v, n)$ returns $(\langle n.\mathrm{id} :: v.\mathrm{nodes}\rangle, \mathrm{true})$ if $n$ is eligible and $n.\mathrm{id} \notin v.\mathrm{nodes}$, and $(v, \mathrm{false})$ otherwise.

**Election quorum.** An election strategy $es$ is an arbitrary Boolean function $f_{es}$ of seven arguments.
$$\mathrm{isElectionQuorum}(es, cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{A}(cs)) \wedge f_{es}(cs.\mathrm{localNode}, cs.\mathrm{currentTerm}, \mathrm{lat}(cs), \mathrm{lav}(cs), \mathrm{C}(cs), \mathrm{A}(cs), v).$$

**Joins.** A join $j$ has two nodes, $j.\mathrm{sourceNode}$ and $j.\mathrm{targetNode}$, a term $j.\mathrm{term} \in \mathbb{N}$, $j.\mathrm{lastAcceptedTerm} \in \mathbb{N}$ and $j.\mathrm{lastAcceptedVersion} \in \mathbb{Z}$.

**The handler** $\mathrm{handleJoin}(es, cs, j)$ tests five guards in order. The first one that holds gives $\mathrm{error}$:

1. $j.\mathrm{term} \ne cs.\mathrm{currentTerm}$;
2. $\neg cs.\mathrm{startedJoinSinceLastReboot}$;
3. $j.\mathrm{lastAcceptedTerm} > \mathrm{lat}(cs)$;
4. $j.\mathrm{lastAcceptedTerm} = \mathrm{lat}(cs) \wedge j.\mathrm{lastAcceptedVersion} > \mathrm{lavm}(cs)$;
5. $\mathrm{isEmpty}(\mathrm{A}(cs))$.

If no guard holds, the handler computes:

- $(v', \mathit{added}) := \mathrm{addVote}(cs.\mathrm{joinVotes}, j.\mathrm{sourceNode})$;
- $\mathit{won} := \mathrm{isElectionQuorum}(es, cs, v')$.

It returns $\mathrm{ok}(cs_2, \mathit{added})$. Here $cs_2$ is $cs$ with $\mathrm{joinVotes} := v'$ and $\mathrm{electionWon} := \mathit{won}$. In addition, $\mathrm{lastPublishedVersion} := \mathrm{lav}(cs)$ if $\mathit{won}$ holds and $cs.\mathrm{electionWon}$ was false.

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $es$: an election strategy, arbitrary;
- $cs$: a coordination state;
- $j$: a join;
- $cs'$: a coordination state;
- $b$: a Boolean.

**Hypothesis.** $h$: $\mathrm{handleJoin}(es, cs, j) = \mathrm{ok}(cs', b)$.

**Conclusion.** The conjunction of:

1. $j.\mathrm{term} = cs.\mathrm{currentTerm}$;
2. $cs.\mathrm{startedJoinSinceLastReboot} = \mathrm{true}$;
3. $\mathrm{isEmpty}(\mathrm{A}(cs)) = \mathrm{false}$;
4. $j.\mathrm{lastAcceptedTerm} < \mathrm{lat}(cs)\ \vee\ \big(j.\mathrm{lastAcceptedTerm} = \mathrm{lat}(cs) \wedge j.\mathrm{lastAcceptedVersion} \le \mathrm{lavm}(cs)\big)$;
5. $cs'.\mathrm{joinVotes} = \mathrm{addVote}(cs.\mathrm{joinVotes}, j.\mathrm{sourceNode}).1$;
6. $b = \mathrm{addVote}(cs.\mathrm{joinVotes}, j.\mathrm{sourceNode}).2$;
7. $cs'.\mathrm{electionWon} = \mathrm{isElectionQuorum}(es, cs, cs'.\mathrm{joinVotes})$, evaluated against the *old* state's configurations, terms and version;
8. $cs'.\mathrm{currentTerm} = cs.\mathrm{currentTerm}$;
9. $cs'.\mathrm{lastAcceptedState} = cs.\mathrm{lastAcceptedState}$;
10. $cs'.\mathrm{localNode} = cs.\mathrm{localNode}$;
11. $cs'.\mathrm{startedJoinSinceLastReboot} = cs.\mathrm{startedJoinSinceLastReboot}$;
12. $cs'.\mathrm{publishVotes} = cs.\mathrm{publishVotes}$;
13. $cs'.\mathrm{lastPublishedConfiguration} = cs.\mathrm{lastPublishedConfiguration}$;
14. $cs'.\mathrm{lastPublishedVersion} = \mathrm{lav}(cs)$ if $cs'.\mathrm{electionWon} = \mathrm{true} \wedge cs.\mathrm{electionWon} = \mathrm{false}$, and $cs'.\mathrm{lastPublishedVersion} = cs.\mathrm{lastPublishedVersion}$ otherwise.

Conjuncts 1–4 are exactly the negations of the five guards. Guards 3 and 4 combine into conjunct 4.

Conjuncts 5, 7 and 8–14 fix all nine fields of $cs'$, and conjunct 6 fixes $b$. Since conjuncts 8–10 keep every input of the election test unchanged, conjunct 7 could equally be evaluated on $cs'$.

## 2. What is not constrained

- **$j.\mathrm{targetNode}$ is never mentioned.** The handler does not check that the join is addressed to this node; Java only asserts it.
- **$j.\mathrm{sourceNode}$ is arbitrary.** If it is ineligible, or its id is already present, then $cs'.\mathrm{joinVotes} = cs.\mathrm{joinVotes}$ and $b = \mathrm{false}$. Even so, the election flag is *recomputed*.
- **There is no invariant hypothesis.** So the statement covers states whose $\mathrm{electionWon}$ disagrees with the quorum test. For such a state, a successful join can turn $\mathrm{electionWon}$ from $\mathrm{true}$ to $\mathrm{false}$. Conjunct 7 then forces that, and conjunct 14 leaves $\mathrm{lastPublishedVersion}$ unchanged. "Won stays won" is a separate theorem with extra hypotheses (`handleJoin_stays_won`).
- **Two different version notions appear.**
  - The freshness comparison in conjunct 4 uses $\mathrm{lavm}(cs)$, the metadata version for term-0 states.
  - The strategy argument inside $\mathrm{isElectionQuorum}$ and the new $\mathrm{lastPublishedVersion}$ in conjunct 14 use the plain $\mathrm{lav}(cs)$.
- **$es$ is arbitrary;** no monotonicity is assumed.
- **Only one direction.** The statement goes from success to these facts; it does not claim that a join satisfying 1–4 succeeds. In fact the guards are exactly 1–4, but the theorem does not state the converse.
- **Not vacuous.** The success hypothesis is satisfiable.

## 3. Plain-language summary

A join is accepted only if:

- its term equals the node's current term;
- the node has received a start-join since its last restart;
- the node's accepted configuration is non-empty;
- the joiner's last-accepted (term, version) is not ahead of the node's own (using the metadata version for term-0 states).

When accepted:

- the joiner is added as a vote if it is eligible and new, and the returned Boolean says whether it was added;
- the election-won flag is recomputed from the new votes;
- the published version is set to the accepted version exactly when the election has just been won;
- nothing else changes.
