# Read-back: `OpenSearchPreVote.round_starts_once`

## Notions used

**Rounds.** A pre-voting round $r$ has five fields: a cluster state, a local node, a list of (sender, response) pairs, and Booleans $r.\mathrm{electionStarted}$ and $r.\mathrm{isClosed}$.

**The handler.** $\mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender})$ returns a triple (new round, start flag, max-term argument). The cases, in order:
1. If $r.\mathrm{isClosed}$: $(r, \mathrm{false}, \text{none})$.
2. If $resp$ is fresher than $r$'s cluster state: $(r, \mathrm{false}, \text{some } resp.\mathrm{currentTerm})$. "Fresher" means a larger last accepted term, or an equal term and a larger last accepted version than the state's version-or-metadata-version.
3. Otherwise let $r_1$ be $r$ with the list updated: the new entry in front, and earlier entries from an equal sender removed. $r_1$ has $r$'s flags.
   - If the votes of $r_1$ are not an election quorum, or $r_1.\mathrm{electionStarted}$ is true: $(r_1, \mathrm{false}, \ldots)$.
   - Otherwise: $(r_1 \text{ with electionStarted} := \mathrm{true}, \mathrm{true}, \ldots)$.

## 1. Declaration

**Binders and hypothesis.**
- $V$: an implicit type;
- $es$: an election strategy;
- $lr, resp$: pre-vote responses;
- $\mathit{sender}$: a discovery node;
- $r$: a round over $V$;
- $h$: $r.\mathrm{electionStarted} = \mathrm{true} \vee r.\mathrm{isClosed} = \mathrm{true}$.

**Conclusion.** Write $(r', b, m) = \mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender})$. Then
$$b = \mathrm{false} \;\wedge\; \big(r'.\mathrm{electionStarted} = \mathrm{true} \vee r'.\mathrm{isClosed} = \mathrm{true}\big).$$

If the round has already started an election or has been closed, then handling any response does not signal an election start, and the resulting round has still started an election or is still closed.

## 2. What is not constrained

- **No reachability hypothesis.** $r$ is arbitrary, and $es$, $lr$, $resp$ and $\mathit{sender}$ are arbitrary.
- **A weak form.** The conclusion keeps only the disjunction. It does not say which flag holds afterwards. By the definition, each flag is in fact preserved individually: a closed round is returned unchanged, and a started round stays started in every branch. The theorem states only the weaker disjunctive form.
- **Other fields.** The conclusion says nothing about $r'$'s other fields. In particular, the list of a started but open round can still grow. It says nothing about $m$.
- **Only the handler.** The theorem covers only $\mathrm{handlePreVoteResponse}$. $\mathrm{close}$ is not mentioned (it trivially keeps $\mathrm{isClosed}$ true). The theorem is a single-step statement; it does not itself assert anything about sequences of steps.
- **Vacuity.** None. The hypothesis is satisfiable by any closed or started round.

## 3. Plain-language summary

Once a round has started an election or been closed, handling one more pre-vote response never starts an election again. The round remains started or closed.
