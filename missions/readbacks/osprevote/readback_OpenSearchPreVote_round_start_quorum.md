# Read-back: `OpenSearchPreVote.round_start_quorum`

## Notions used

**Basics.**
- A discovery node is a pair (node id, cluster-manager-eligible flag $\mathrm{cm}$).
- A pre-vote response has a current term, a last accepted term (both in $\mathbb{N}$) and a last accepted version $\in \mathbb{Z}$.
- A cluster state $s$ has a term, a version and a metadata version, a last committed configuration $s.\mathrm{committed}$ and a last accepted configuration $s.\mathrm{accepted}$.
- $\mathrm{vomv}(s)$ is the metadata version when $s.\mathrm{term} = 0$, and the version otherwise.
- A voting configuration $C$ is a strictly increasing list of node ids. $\mathrm{hasQuorum}(C, X)$ means that strictly more than half of $C$'s ids occur in the list $X$.

**No-fresher.** $\mathrm{NoFresher}(resp, s)$ means
$$resp.\mathrm{lastAcceptedTerm} < s.\mathrm{term} \;\vee\; \big(resp.\mathrm{lastAcceptedTerm} = s.\mathrm{term} \wedge resp.\mathrm{lastAcceptedVersion} \le \mathrm{vomv}(s)\big).$$

**Votes.** $\mathrm{votes}(r)$ is the set (a duplicate-free list) of ids of the cluster-manager-eligible senders in $r.\mathrm{preVotesReceived}$.

**Election quorum.** $\mathrm{isElectionQuorumFor}(es, n, t, a, w, C_c, C_a, v)$ is the conjunction of three tests:
- $v$ has a quorum of $C_c$;
- $v$ has a quorum of $C_a$;
- the strategy's arbitrary extra test $\mathrm{extra}_{es}(n, t, a, w, C_c, C_a, v)$ holds.

**The handler.** $\mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender})$ returns a triple (new round, start flag, max-term argument). Write $s = r.\mathrm{clusterState}$. The cases, in order:
1. If $r.\mathrm{isClosed}$: $(r, \mathrm{false}, \text{none})$.
2. If $resp$ is not $\mathrm{NoFresher}(resp, s)$: $(r, \mathrm{false}, \text{some } resp.\mathrm{currentTerm})$.
3. Otherwise let $r_1$ be $r$ with list $(\mathit{sender}, resp) :: [p \in r.\mathrm{preVotesReceived} \mid p.1 \neq \mathit{sender}]$, and let
   $$Q = \mathrm{isElectionQuorumFor}(es, r.\mathrm{localNode}, lr.\mathrm{currentTerm}, lr.\mathrm{lastAcceptedTerm}, lr.\mathrm{lastAcceptedVersion}, s.\mathrm{committed}, s.\mathrm{accepted}, \mathrm{votes}(r_1)).$$
   - If $Q$ is false, or $r.\mathrm{electionStarted}$ is already true: $(r_1, \mathrm{false}, \text{some } resp.\mathrm{currentTerm})$.
   - Otherwise: $(r_1 \text{ with electionStarted} := \mathrm{true},\ \mathrm{true},\ \text{some } resp.\mathrm{currentTerm})$.

## 1. Declaration

**Binders and hypothesis.**
- $V$: an implicit type;
- $es$: an election strategy;
- $lr, resp$: pre-vote responses ($lr$ is the requester's "local response");
- $\mathit{sender}$: a discovery node;
- $r, r'$: rounds over $V$;
- $m$: "none" or "some $t$";
- $h$: $\mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender}) = (r', \mathrm{true}, m)$.

**Conclusion.** Seven conjuncts:
1. $r.\mathrm{isClosed} = \mathrm{false}$;
2. $r.\mathrm{electionStarted} = \mathrm{false}$;
3. $r'.\mathrm{electionStarted} = \mathrm{true}$;
4. $\mathrm{NoFresher}(resp, r.\mathrm{clusterState})$;
5. $r'.\mathrm{clusterState} = r.\mathrm{clusterState}$;
6. $r'.\mathrm{localNode} = r.\mathrm{localNode}$;
7. $\mathrm{isElectionQuorumFor}(es, r.\mathrm{localNode}, lr.\mathrm{currentTerm}, lr.\mathrm{lastAcceptedTerm}, lr.\mathrm{lastAcceptedVersion}, r.\mathrm{clusterState}.\mathrm{committed}, r.\mathrm{clusterState}.\mathrm{accepted}, \mathrm{votes}(r')) = \mathrm{true}$.

Conjunct 7, unfolded, says three things:
- the eligible-sender ids of $r'$ form a strict majority of the last committed configuration of $r$'s cluster state;
- they also form a strict majority of its last accepted configuration;
- the strategy's extra test holds for these arguments.

Here $\mathrm{votes}(r') = \mathrm{votes}(r_1)$, because $r'$ differs from $r_1$ only in the started flag. So it is computed from the updated list, with the new entry in front and older entries from the same sender removed.

## 2. What is not constrained

- **No reachability hypothesis.** $r$ is an arbitrary round. The theorem is a one-step inversion of the handler's definition.
- **$m$.** It appears only in the hypothesis. The conclusion says nothing about it (in fact it is "some $resp.\mathrm{currentTerm}$").
- **What is not described.** The conclusion does not describe $r'.\mathrm{preVotesReceived}$ or $r'.\mathrm{isClosed}$. It does not say that the sender's own vote was counted; the sender may be ineligible and contribute no vote.
- **$lr$.** It is arbitrary. Its three fields enter only as the strategy's term and version arguments, exactly as in the handler. Under a strategy that ignores those arguments, such as the default one, $lr$ has no effect.
- **Vacuity.** None. The hypothesis is satisfiable. For example, take a one-node configuration $\{1\}$ in both slots, cluster state term $0$, versions $0$, and an open, unstarted round with an empty list. Then a response $\langle 0,0,0\rangle$ from $\langle 1, \mathrm{true}\rangle$ under the default strategy yields the start flag true. I checked this by evaluation.

## 3. Plain-language summary

If handling one pre-vote response makes a round start an election, then the round was open and had not started one before, and the response was no fresher than the round's accepted state. The resulting round is marked as started and keeps the same accepted state and local node. Its updated pre-votes form an election quorum: a majority of both the last committed and the last accepted configuration, plus the strategy's extra condition, evaluated with the given local response.
