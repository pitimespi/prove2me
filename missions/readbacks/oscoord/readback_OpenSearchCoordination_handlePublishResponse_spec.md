# Read-back: `OpenSearchCoordination.handlePublishResponse_spec`

## Notions used

**Coordination states.** A coordination state $cs$ has nine fields:

- $cs.\mathrm{localNode}$, a node with an id and an eligibility flag;
- $cs.\mathrm{currentTerm} \in \mathbb{N}$;
- $cs.\mathrm{lastAcceptedState}$;
- $cs.\mathrm{joinVotes}$ and $cs.\mathrm{publishVotes}$, vote collections (lists of ids);
- $cs.\mathrm{startedJoinSinceLastReboot}$ and $cs.\mathrm{electionWon}$, Booleans;
- $cs.\mathrm{lastPublishedVersion} \in \mathbb{Z}$;
- $cs.\mathrm{lastPublishedConfiguration}$.

$\mathrm{C}(cs)$ is the last committed configuration of $cs.\mathrm{lastAcceptedState}$.

**Votes and quorums.**

- $\mathrm{isQuorum}(v, c)$ holds iff strictly more than half of the ids of configuration $c$ occur in $v.\mathrm{nodes}$.
- $\mathrm{addVote}(v, n)$ returns $(\langle n.\mathrm{id} :: v.\mathrm{nodes}\rangle, \mathrm{true})$ if $n$ is eligible and $n.\mathrm{id} \notin v.\mathrm{nodes}$, and $(v, \mathrm{false})$ otherwise.
- $\mathrm{isPublishQuorum}(cs, v) = \mathrm{isQuorum}(v, \mathrm{C}(cs)) \wedge \mathrm{isQuorum}(v, cs.\mathrm{lastPublishedConfiguration})$.

**Messages.**

- A publish response $r$ has $r.\mathrm{term} \in \mathbb{N}$ and $r.\mathrm{version} \in \mathbb{Z}$.
- A commit request is a triple $\langle \mathrm{sourceNode}, \mathrm{term} \in \mathbb{N}, \mathrm{version} \in \mathbb{Z}\rangle$.

**The handler** $\mathrm{handlePublishResponse}(cs, n, r)$ tests three guards in order. The first one that holds yields $\mathrm{error}$:

1. $\neg cs.\mathrm{electionWon}$;
2. $r.\mathrm{term} \ne cs.\mathrm{currentTerm}$;
3. $r.\mathrm{version} \ne cs.\mathrm{lastPublishedVersion}$.

Otherwise, let $v' = \mathrm{addVote}(cs.\mathrm{publishVotes}, n).1$ and $cs^\ast = cs$ with $\mathrm{publishVotes} := v'$. The result is:

- $\mathrm{ok}(cs^\ast, \mathrm{some}\ \langle cs.\mathrm{localNode}, r.\mathrm{term}, r.\mathrm{version}\rangle)$ if $\mathrm{isPublishQuorum}(cs^\ast, v')$;
- $\mathrm{ok}(cs^\ast, \mathrm{none})$ otherwise.

## 1. Declaration

**Binders.**
- $V$ (implicit);
- $cs$: a coordination state;
- $n$ (`src`): a node;
- $r$: a publish response;
- $cs'$: a coordination state;
- $o$: an optional commit request.

**Hypothesis.** $h$: $\mathrm{handlePublishResponse}(cs, n, r) = \mathrm{ok}(cs', o)$.

**Conclusion.** The conjunction of:

1. $cs.\mathrm{electionWon} = \mathrm{true}$;
2. $r.\mathrm{term} = cs.\mathrm{currentTerm}$;
3. $r.\mathrm{version} = cs.\mathrm{lastPublishedVersion}$;
4. $cs' = cs$ with $\mathrm{publishVotes} := \mathrm{addVote}(cs.\mathrm{publishVotes}, n).1$;
5. $\forall c,\ o = \mathrm{some}\ c \to$ the following three facts hold:
   - $c = \langle cs.\mathrm{localNode},\ cs.\mathrm{currentTerm},\ cs.\mathrm{lastPublishedVersion}\rangle$;
   - $\mathrm{isQuorum}(cs'.\mathrm{publishVotes}, \mathrm{C}(cs)) = \mathrm{true}$;
   - $\mathrm{isQuorum}(cs'.\mathrm{publishVotes}, cs.\mathrm{lastPublishedConfiguration}) = \mathrm{true}$.

Conjuncts 1–3 are the negations of the guards. Conjunct 4 determines $cs'$ completely. Conjunct 5 constrains the returned commit request, if there is one: its term and version equal the node's current term and last published version, and the updated publish votes form a quorum of both the committed and the last *published* configuration (not the accepted one).

## 2. What is not constrained

- **When $o = \mathrm{none}$, nothing is claimed.** The theorem does not say that "none" means the votes fail to be a publish quorum. Equally, it does not say that a commit request is returned whenever a quorum is reached, although by definition the handler is deterministic and does return one.
- **$n$ is arbitrary.** If $n$ is ineligible or already counted, the votes are unchanged. If a quorum already holds, a commit request is returned again; the statement permits this.
- **The commit's source node is the local node.** The responding node $n$ does not appear in the returned request.
- **No assumption on $cs$** beyond success, and no invariant.
- **Not vacuous.** The success hypothesis is satisfiable, for example by a node that has won the election and receives a response matching its current term and published version.

## 3. Plain-language summary

A node processes a publish response only if:

- it has won the election;
- the response's term equals its current term;
- the response's version equals its last published version.

The only state change is adding the responder (if eligible) to the publish votes. If a commit request is returned, it comes from the local node for the current term and the last published version, and the updated publish votes form a quorum of both the last committed and the last published configurations.
