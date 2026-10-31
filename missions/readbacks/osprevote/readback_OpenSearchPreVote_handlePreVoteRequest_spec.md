# Read-back: `OpenSearchPreVote.handlePreVoteRequest_spec`

## Notions used

**Discovery nodes.** A discovery node is a pair (node id $\in \mathbb{N}$, Boolean "cluster-manager-eligible" flag). Two discovery nodes are equal iff both components are equal.

**Messages and collector state.**
- A pre-vote request $req$ has a source node $req.\mathrm{sourceNode}$ and a term $req.\mathrm{currentTerm} \in \mathbb{N}$.
- A pre-vote response is a triple $\langle \mathrm{currentTerm} \in \mathbb{N},\ \mathrm{lastAcceptedTerm} \in \mathbb{N},\ \mathrm{lastAcceptedVersion} \in \mathbb{Z}\rangle$.
- A collector state $st$ has a known leader $st.\mathrm{leader}$ ("none", or "some $l$" for a discovery node $l$) and a stored response $st.\mathrm{response}$.

**The handler.** $\mathrm{handlePreVoteRequest}(\mathit{healthy}, st, req)$ returns either an error string or a response:
- If $\mathit{healthy}$ is false: the error "rejecting on unhealthy node".
- Otherwise, if $st.\mathrm{leader} = \text{none}$: success with $st.\mathrm{response}$.
- Otherwise, if $st.\mathrm{leader} = \text{some } l$ with $l = req.\mathrm{sourceNode}$: success with $st.\mathrm{response}$.
- Otherwise: the error "rejecting as there is already a leader".

## 1. Declaration

**Binders.** There are no hypotheses.
- $\mathit{healthy}$: a Boolean;
- $st$: a collector state;
- $req$: a pre-vote request;
- $resp$: a pre-vote response.

**Conclusion.**
$$\mathrm{handlePreVoteRequest}(\mathit{healthy}, st, req) = \mathrm{ok}(resp) \iff \mathit{healthy} = \mathrm{true} \;\wedge\; \big(st.\mathrm{leader} = \text{none} \vee st.\mathrm{leader} = \text{some } req.\mathrm{sourceNode}\big) \;\wedge\; resp = st.\mathrm{response}.$$

In words, the handler returns success with $resp$ exactly when three things hold:
- the node is healthy;
- the node knows no leader, or the leader it knows is exactly the requesting node (same id and same flag);
- $resp$ is the node's stored response.

## 2. What is not constrained

- **The request's term.** $req.\mathrm{currentTerm}$ does not occur on the right-hand side. The handler never reads it.
- **Leader equality.** It is structural on (id, flag). A known leader with the requester's id but the opposite flag counts as "another leader", and the request is refused.
- **Errors.** The theorem says nothing about the error messages and does not separate the two refusal reasons. The handler always returns either success or an error. So for given $(\mathit{healthy}, st, req)$, the theorem also implies: the handler is an error iff the first two conjuncts fail. When it succeeds, the value is exactly $st.\mathrm{response}$.
- **Side effects.** The Java handler's side effect (raising `maxTermSeen` to the request's term) is not modelled by the function, so the theorem does not mention it.
- **Vacuity.** There are no hypotheses, so nothing can be vacuous. Both sides are satisfiable; for example, take $\mathit{healthy} = \mathrm{true}$, $st.\mathrm{leader} = \text{none}$ and $resp = st.\mathrm{response}$.

## 3. Plain-language summary

A node grants a pre-vote request if and only if it is healthy and either knows no leader or its known leader is the requester itself. When it grants, it returns its stored response unchanged. The term carried by the request plays no role in the decision.
