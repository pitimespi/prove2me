# Read-back: `OpenSearchPreVote.no_disruption`

## Notions used

**Discovery nodes.** A discovery node $n$ is a pair: a node id $n.\mathrm{id} \in \mathbb{N}$ and a Boolean flag $n.\mathrm{cm}$ ("cluster-manager-eligible"). Two discovery nodes are equal iff both components are equal.

**Configurations and quorums.** A voting configuration $C$ is a strictly increasing (hence duplicate-free) list of node ids $C.\mathrm{ids}$. For a list $X$ of node ids,
$$\mathrm{hasQuorum}(C, X) \iff 2\cdot|\{x \in C.\mathrm{ids} : x \in X\}| > |C.\mathrm{ids}|.$$

**Cluster states.** A cluster state $s$ has, among other fields, a last committed configuration $s.\mathrm{committed}$ and a last accepted configuration $s.\mathrm{accepted}$.

**Requests, collector states, and the request handler.**
- A pre-vote request $\langle c, t\rangle$ consists of a source node $c$ and a term $t$.
- A collector state $st$ has a known leader $st.\mathrm{leader}$ ("none", or "some $l$") and a stored response $st.\mathrm{response}$.
- $\mathrm{handlePreVoteRequest}(\mathit{healthy}, st, \langle c, t\rangle)$ returns success with $st.\mathrm{response}$ iff $\mathit{healthy}$ is true and ($st.\mathrm{leader} = \text{none}$ or $st.\mathrm{leader} = \text{some } c$). Otherwise it returns an error. The term $t$ is never read.

**Rounds.** A round $r$ has a cluster state $r.\mathrm{clusterState}$, a local node $r.\mathrm{localNode}$, a list of (sender, response) pairs, and Booleans $\mathrm{electionStarted}$ and $\mathrm{isClosed}$. $\mathrm{votes}(r)$ is the set of ids of the cluster-manager-eligible senders in the list.

**The response handler.** $\mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender})$ returns (new round, start flag, max-term argument). Write $s = r.\mathrm{clusterState}$.
- If $r$ is closed, or $resp$ is fresher than $s$, the round is unchanged and the flag is false.
- Otherwise the list becomes $(\mathit{sender}, resp)$ followed by the old entries from senders $\neq \mathit{sender}$; call this round $r_1$. The flag is true iff both of these hold:
  - $r$ had not started an election;
  - $\mathrm{hasQuorum}(s.\mathrm{committed}, \mathrm{votes}(r_1))$, $\mathrm{hasQuorum}(s.\mathrm{accepted}, \mathrm{votes}(r_1))$ and the strategy's arbitrary extra test all hold.

  When the flag is true, $\mathrm{electionStarted}$ becomes true.

**Reachability.** $\mathrm{RoundReachable}_{es, D}$ is the least predicate on rounds closed under three rules:
- every $\mathrm{start}(s, n) = \langle s, n, [\,], \mathrm{false}, \mathrm{false}\rangle$ is reachable;
- handling, with any local response, of any $(\mathit{sender}, resp)$ with $D(\mathit{sender}, resp)$;
- closing.

## 1. Declaration

**Binders and hypotheses, in order.**
- $V$: an implicit type.
- $es$: an election strategy, arbitrary.
- $\mathit{healthy}$: a function from discovery nodes to Booleans (each node's health).
- $st$: a function from discovery nodes to collector states (each node's known leader and stored response).
- $c$: a discovery node (the requester named in the pre-vote request).
- $t \in \mathbb{N}$: the request's term.
- $s$: a cluster state over $V$.
- $L$: a list of node ids.
- **$hL$**: $\mathrm{hasQuorum}(s.\mathrm{committed}, L) = \mathrm{true} \;\vee\; \mathrm{hasQuorum}(s.\mathrm{accepted}, L) = \mathrm{true}$. So strictly more than half of the ids of $s$'s last committed configuration lie in $L$, or strictly more than half of the ids of its last accepted configuration do.
- **$hfollow$**: for every discovery node $n$ (with either flag) such that $n.\mathrm{id} \in L$,
  $$\mathit{healthy}(n) = \mathrm{false} \;\vee\; \exists\, l,\ st(n).\mathrm{leader} = \text{some } l \wedge l \neq c.$$
  Every node whose id is in $L$ is unhealthy or knows a leader different from $c$. "Different" means different id or different flag. By the handler's definition, this is the same as saying every such node refuses the request $\langle c, t\rangle$.
- $r$: a round over $V$.
- **$hr$**: $\mathrm{RoundReachable}_{es, D}(r)$, where
  $$D(n, resp) \;:\iff\; \mathrm{handlePreVoteRequest}(\mathit{healthy}(n), st(n), \langle c, t\rangle) = \mathrm{ok}(resp).$$
  Unfolded, $D(n, resp)$ holds iff all of these hold:
  - $\mathit{healthy}(n)$;
  - $st(n).\mathrm{leader} \in \{\text{none}, \text{some } c\}$;
  - $resp = st(n).\mathrm{response}$.

  So the only deliveries are of the stored responses of the nodes willing to answer $c$.
- **$hs$**: $r.\mathrm{clusterState} = s$.

**Conclusion.**
$$r.\mathrm{electionStarted} = \mathrm{false} \;\wedge\; \forall\, lr\ resp\ \mathit{sender},\ \mathrm{handlePreVoteRequest}(\mathit{healthy}(\mathit{sender}), st(\mathit{sender}), \langle c, t\rangle) = \mathrm{ok}(resp) \rightarrow \big(\mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender})\big).2.1 = \mathrm{false}.$$
- (a) The round has never started an election.
- (b) Handling one more response that some sender would genuinely give to $\langle c, t\rangle$ does not start an election either, for any local response $lr$.

## 2. What is not constrained

- **The strategy.** $es$ is arbitrary, even non-monotone. The conclusion can hold for every strategy because the election quorum requires *both* configuration majorities, and $hL$ blocks one of them. Here is my reading of why the hypotheses fit together (not a proof):
  - No node with an id in $L$ can ever deliver.
  - So $\mathrm{votes}$ stays disjoint from $L$.
  - A set disjoint from a strict majority of a duplicate-free configuration cannot itself be a strict majority of it.
- **The term $t$.** It never matters, because the request handler does not read it.
- **The local node.** $r.\mathrm{localNode}$ is unconstrained, and it is **not** required to equal $c$. The node named as requester in the requests and the round's own local node may differ.
- **Nodes outside $L$.** They are unconstrained. They may be healthy and leaderless, or follow $c$, and then they deliver and their votes count.
- **The list $L$.** $L$ may contain duplicates or ids outside both configurations. Only one of the two configurations needs to have its majority inside $L$.
- **The requester itself.** If $c.\mathrm{id} \in L$, then $hfollow$ also constrains $c$'s own health and collector state: $c$ must be unhealthy or follow another leader. If $c.\mathrm{id} \notin L$, $c$'s own answer is unconstrained.
- **Static model.** Health and collector states are fixed functions for the entire round. They do not change while the round runs. All deliveries answer the same request $\langle c, t\rangle$.
- **Scope.** The statement concerns only the round's start flag.
  - It says nothing about the responders' `updateMaxTermSeen`. In Java, `handlePreVoteRequest` raises every responder's `maxTermSeen` to $t$ (PreVoteCollector.java:134). That includes a current leader, which then moves to a higher term and starts an election itself when $t$ exceeds its term (Coordinator.java:564–573). The module docstring places this outside the functions.
  - It says nothing about the effect of the round's own `updateMaxTermSeen` calls.
- **Vacuity.** None. The hypotheses are jointly satisfiable in a non-trivial way, which I checked by evaluation:
  - take configuration $\{1,2,3\}$ in both slots and $L = [1,2]$;
  - nodes with ids $1$ and $2$ follow leader $\langle 9, \mathrm{true}\rangle$;
  - $c = \langle 3, \mathrm{true}\rangle$ is healthy with no leader;
  - $c$ answers its own request, giving votes $\{3\}$: no quorum and no start.

  Also, $hr$ and $hs$ hold for $\mathrm{start}(s, n)$ for any $n$.

## 3. Plain-language summary

Suppose a majority of either the last committed or the last accepted configuration of state $s$ consists of nodes that are unhealthy or already follow a leader other than $c$. Then no pre-voting round over $s$ that collects only genuine answers to $c$'s request ever starts an election, and one more genuine answer would not start one either. The statement is about the round's quorum count with every node's state frozen. It does not cover Java's term-raising side effects of pre-vote requests.
