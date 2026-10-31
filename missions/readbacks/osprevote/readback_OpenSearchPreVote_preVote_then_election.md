# Read-back: `OpenSearchPreVote.preVote_then_election`

## Notions used

**Discovery nodes, configurations, cluster states.**
- A discovery node $n$ is a pair: a node id $n.\mathrm{id} \in \mathbb{N}$ and a Boolean flag $n.\mathrm{cm}$ ("cluster-manager-eligible"). Equality compares both components.
- A voting configuration $C$ is a strictly increasing list of node ids. $\mathrm{hasQuorum}(C, X)$ means that strictly more than half of $C$'s ids occur in the list $X$; the empty configuration never has a quorum.
- A cluster state $s$ has a term $s.\mathrm{term} \in \mathbb{N}$, a version and a metadata version in $\mathbb{Z}$, a last committed configuration $s.\mathrm{committed}$, a last accepted configuration $s.\mathrm{accepted}$, and other fields.
- $\mathrm{vomv}(s)$ is the metadata version if $s.\mathrm{term} = 0$, and the version otherwise.

**Coordination states.** A coordination state $cs$ has these fields:
- a local node $cs.\mathrm{localNode}$ and a current term $cs.\mathrm{currentTerm}$;
- a last accepted state $cs.\mathrm{las}$;
- a vote collection $cs.\mathrm{joinVotes}$ (a list of node ids);
- Booleans $cs.\mathrm{startedJoinSinceLastReboot}$ and $cs.\mathrm{electionWon}$;
- publication fields.

Its pre-vote response is
$$\mathrm{preVoteResponseOf}(cs) = \langle cs.\mathrm{currentTerm},\ cs.\mathrm{las}.\mathrm{term},\ \mathrm{vomv}(cs.\mathrm{las})\rangle.$$

**Start-join.** A start-join request $\langle src, T\rangle$ has a source node and a term. $\mathrm{handleStartJoin}(cs, \langle src, T\rangle)$ behaves as follows:
- If $T \le cs.\mathrm{currentTerm}$, it is an error.
- Otherwise it succeeds with $(cs', j)$.
  - $cs'$ is $cs$ with current term $T$, startedJoinSinceLastReboot true, electionWon false, empty join votes, empty publish votes, last published version $0$, and last published configuration $cs.\mathrm{las}.\mathrm{accepted}$. The local node and the last accepted state are unchanged.
  - $j$ is the join $\langle cs.\mathrm{localNode},\ src,\ T,\ cs.\mathrm{las}.\mathrm{term},\ \mathrm{vomv}(cs.\mathrm{las})\rangle$, read as (source, target, term, last accepted term, last accepted version).

**Join handling with the default strategy.** $\mathrm{handleJoin}(\mathrm{DEFAULT}, cs, j)$ rejects with an error, leaving no state, if any of these holds:
1. $j.\mathrm{term} \neq cs.\mathrm{currentTerm}$;
2. startedJoinSinceLastReboot is false;
3. $j.\mathrm{lastAcceptedTerm} > cs.\mathrm{las}.\mathrm{term}$;
4. the terms are equal and $j.\mathrm{lastAcceptedVersion} > \mathrm{vomv}(cs.\mathrm{las})$;
5. $cs.\mathrm{las}.\mathrm{accepted}$ is empty.

Otherwise it adds $j.\mathrm{source}.\mathrm{id}$ to the join votes, if the source is cluster-manager-eligible and not already present. It then sets
$$\mathrm{electionWon} := \mathrm{hasQuorum}(cs.\mathrm{las}.\mathrm{committed}, \mathrm{votes}) \wedge \mathrm{hasQuorum}(cs.\mathrm{las}.\mathrm{accepted}, \mathrm{votes}).$$
The default strategy's extra test is constantly true. Under certain conditions the last published version also changes. The join's target is never checked.

$\mathrm{handleJoins}(\mathrm{DEFAULT}, cs, js)$ applies $\mathrm{handleJoin}$ to the joins of $js$ from left to right, keeping the state unchanged on each rejection.

**Election term.** $\mathrm{startElectionTerm}(t_c, t_m) = \max(t_c, t_m) + 1$.

**Rounds.**
- A round $r$ has a cluster state $r.\mathrm{clusterState}$, a local node $r.\mathrm{localNode}$, a list $r.\mathrm{preVotesReceived}$ of (sender, response) pairs, and Booleans $\mathrm{electionStarted}$ and $\mathrm{isClosed}$.
- $\mathrm{RoundReachable}_{es, D}$ is the least predicate containing every $\mathrm{start}(s, n)$, closed under handling (with an arbitrary local response) any $(\mathit{sender}, resp)$ with $D(\mathit{sender}, resp)$, and closed under closing.
- Handling an open round stores a response only if it is no fresher than the round's cluster state, that is, lexicographically $(resp.\mathrm{lastAcceptedTerm}, resp.\mathrm{lastAcceptedVersion}) \le (s.\mathrm{term}, \mathrm{vomv}(s))$. It replaces any earlier entry from an equal sender.
- It sets $\mathrm{electionStarted}$ once the eligible senders' ids form an election quorum, which under the default strategy means majorities of both $s.\mathrm{committed}$ and $s.\mathrm{accepted}$.

## 1. Declaration

**Binders and hypotheses, in order.** Write $T := \mathrm{startElectionTerm}(csc.\mathrm{currentTerm}, \mathit{maxTermSeen}) = \max(csc.\mathrm{currentTerm}, \mathit{maxTermSeen}) + 1$.
- $V$: an implicit type.
- $csc$: a coordination state over $V$ (the candidate).
- $\mathit{node}$: a function from discovery nodes to coordination states over $V$ (every node's coordination state).
- $r$: a round over $V$.
- **$hr$**: $\mathrm{RoundReachable}_{\mathrm{DEFAULT}, D}(r)$, where $D(n, resp) :\iff \mathit{node}(n).\mathrm{localNode} = n \wedge \mathrm{preVoteResponseOf}(\mathit{node}(n)) = resp$. A delivery from $n$ must be the genuine pre-vote response of $n$'s coordination state, and that state's local node must be $n$ itself (same id and flag).
- **$hstate$**: $r.\mathrm{clusterState} = csc.\mathrm{las}$.
- **$hlocal$**: $r.\mathrm{localNode} = csc.\mathrm{localNode}$.
- **$hstarted$**: $r.\mathrm{electionStarted} = \mathrm{true}$.
- $\mathit{maxTermSeen} \in \mathbb{N}$.
- **$hseen$**: $\forall p \in r.\mathrm{preVotesReceived},\ p.2.\mathrm{currentTerm} \le \mathit{maxTermSeen}$.
- $csc_1$: a coordination state; $j_0$: a join.
- **$hsj$**: $\mathrm{handleStartJoin}(csc, \langle csc.\mathrm{localNode}, T\rangle) = \mathrm{ok}(csc_1, j_0)$.
- $js$: a list of joins.
- **$hjs$**: $\forall j \in js,\ j.\mathrm{term} \le T$.

**Conclusion.** (A) $\wedge$ (B), where:

- **(A)** $\forall p \in r.\mathrm{preVotesReceived},\ \exists\, cs'\, j,\ \mathrm{handleStartJoin}(\mathit{node}(p.1), \langle csc.\mathrm{localNode}, T\rangle) = \mathrm{ok}(cs', j)$.

  By the definition of $\mathrm{handleStartJoin}$, this says $\mathit{node}(p.1).\mathrm{currentTerm} < T$ for every recorded pre-voter: every recorded pre-voter accepts the candidate's start-join request in term $T$.

- **(B)** $\Big(\forall p \in r.\mathrm{preVotesReceived},\ \forall cs'\, j,\ \mathrm{handleStartJoin}(\mathit{node}(p.1), \langle csc.\mathrm{localNode}, T\rangle) = \mathrm{ok}(cs', j) \rightarrow j \in js\Big) \;\rightarrow\; \mathrm{handleJoins}(\mathrm{DEFAULT}, csc_1, js).\mathrm{electionWon} = \mathrm{true}$.

  - The antecedent: for every recorded pre-voter, the join it produces in answer to $\langle csc.\mathrm{localNode}, T\rangle$ is an element of $js$. That join is $\langle \mathit{node}(p.1).\mathrm{localNode},\ csc.\mathrm{localNode},\ T,\ \mathit{node}(p.1).\mathrm{las}.\mathrm{term},\ \mathrm{vomv}(\mathit{node}(p.1).\mathrm{las})\rangle$.
  - The consequent: after the candidate's post-start-join state $csc_1$ handles the joins of $js$ in order, its electionWon flag is true.
  - $csc_1$ starts with electionWon false, and only an accepted join sets the flag. So the consequent means: some join of $js$ was accepted, and the last accepted one left join votes with majorities of both configurations of $csc.\mathrm{las}$.

**What $hsj$ amounts to.** $T > csc.\mathrm{currentTerm}$ always holds, so $\mathrm{handleStartJoin}$ always succeeds here. $hsj$ is no restriction on $csc$. It only names the result:
- $csc_1$ is $csc$ with current term $T$, startedJoinSinceLastReboot true, electionWon false, empty vote collections, last published version $0$ and last published configuration $csc.\mathrm{las}.\mathrm{accepted}$;
- $j_0 = \langle csc.\mathrm{localNode}, csc.\mathrm{localNode}, T, csc.\mathrm{las}.\mathrm{term}, \mathrm{vomv}(csc.\mathrm{las})\rangle$.

## 2. What is not constrained

- **Strategy.** The election strategy is fixed to `DEFAULT_INSTANCE`, both in the round and in $\mathrm{handleJoins}$. Nothing is claimed for other strategies.
- **Frozen states.** There is a single function $\mathit{node}$. Each pre-voter's coordination state is the same when it answers the pre-vote and when it receives the start-join.
- **The candidate's own entry.** $\mathit{node}(csc.\mathrm{localNode})$ is not tied to $csc$. If the candidate's own pre-vote is recorded, it comes from $\mathit{node}(csc.\mathrm{localNode})$, which may be a different state from $csc$. The candidate's own join $j_0$ is not required to be in $js$.
- **Delivery is more permissive than Java.** $D$ does not involve the pre-vote request handler. Recorded pre-voters need not be healthy, and need not be leaderless or following the candidate. So the theorem covers rounds that Java's request handling would not produce.
- **$hlocal$.** Under the default strategy the local node is only passed to the strategy's extra test, which ignores it. So $hlocal$ appears not to be needed for the conclusion. This is my reading, not a proof.
- **$hseen$.** It is an assumption standing in for the max-term bookkeeping. Java raises `maxTermSeen` with each response's term (PreVoteCollector.java:231), but no definition here tracks it. It is required only for the recorded entries, not for dropped or fresher responses.
- **$hstate$.** The candidate's last accepted state at election time must equal the round's cluster state, that is, unchanged since the round started. The candidate's current term is otherwise free.
- **Java's election guards.** Java's `startElection` checks mode `CANDIDATE` and `localNodeMayWinElection` (Coordinator.java:587–591). Neither is a hypothesis; the definition `nodeMayWinElection` is not used. Likewise, the actual sending of start-join requests to the discovered nodes is not modelled. The theorem directly assumes $\mathrm{handleStartJoin}$ is applied.
- **The list $js$.** Beyond $hjs$, $js$ is arbitrary: extra joins with any source, any target and any term $\le T$, in any order. The conclusion asserts electionWon regardless. Joins with term $< T$ are rejected by guard 1, so they have no effect. Joins' targets are never checked.
- **The antecedent of (B).** It demands the joins of *all* recorded pre-voters, including ineligible ones whose joins add no vote. That is stronger than necessary, and harmless.
- **Scope of the conclusion.** It is about the candidate's coordination-state flag electionWon. It says nothing about Coordinator mode (becoming leader) or about publishing a first state.
- **Consequences of $hstarted$.** With $hr$, $hstarted$ forces a non-empty recorded list and non-empty configurations, because no vote set is a quorum of the empty configuration.
- **Vacuity.** None. I checked a witness by evaluation:
  - a one-node configuration $\{1\}$ in both slots, state term $0$, versions $0$;
  - $csc$ with local node $\langle 1, \mathrm{true}\rangle$ and current term $0$, and $\mathit{node}(n) = csc$ with local node $n$;
  - one delivery from $\langle 1, \mathrm{true}\rangle$ starts the election;
  - $\mathit{maxTermSeen} = 0$, $T = 1$, and $js = [j_0]$ yields electionWon true.

  With $js = [\,]$ the antecedent of (B) fails, because the recorded pre-voter's join is missing, so (B) holds only vacuously there. The antecedent is what makes (B) informative.

## 3. Plain-language summary

Take a pre-voting round under the default election strategy. Its recorded pre-votes are the genuine responses of the senders' coordination states, and the round has started an election. The candidate's accepted state is the round's state, and it sends a start-join in term $\max(\text{currentTerm}, \mathit{maxTermSeen}) + 1$, where $\mathit{maxTermSeen}$ bounds every recorded pre-voter's term. Then every recorded pre-voter accepts that start-join. And if the candidate then handles a list of joins (all of term at most that term) that contains every recorded pre-voter's resulting join, its coordination state has won the election. This assumes the pre-voters' states do not change between the pre-vote and the start-join.
