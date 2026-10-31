# Read-back: `OpenSearchPreVote.round_entries`

## Notions used

**Discovery nodes, responses, cluster states.**
- A discovery node is a pair (node id $\in \mathbb{N}$, Boolean cluster-manager-eligible flag). Equality is equality of both components.
- A pre-vote response has a current term $\in \mathbb{N}$, a last accepted term $\in \mathbb{N}$ and a last accepted version $\in \mathbb{Z}$.
- A cluster state $s$ has, among other fields, a term $s.\mathrm{term} \in \mathbb{N}$, a version and a metadata version in $\mathbb{Z}$, and two voting configurations $s.\mathrm{committed}$ and $s.\mathrm{accepted}$.
- $\mathrm{vomv}(s)$ is the metadata version if $s.\mathrm{term} = 0$, and the version otherwise.

**No-fresher.** $\mathrm{NoFresher}(resp, s)$ means
$$resp.\mathrm{lastAcceptedTerm} < s.\mathrm{term} \;\vee\; \big(resp.\mathrm{lastAcceptedTerm} = s.\mathrm{term} \wedge resp.\mathrm{lastAcceptedVersion} \le \mathrm{vomv}(s)\big).$$

**Rounds and the response handler.** A round $r$ has five fields: a cluster state $r.\mathrm{clusterState}$, a local node, a list $r.\mathrm{preVotesReceived}$ of (sender, response) pairs, and Booleans $\mathrm{electionStarted}$ and $\mathrm{isClosed}$. $\mathrm{start}(s, n) = \langle s, n, [\,], \mathrm{false}, \mathrm{false}\rangle$, and $\mathrm{close}(r)$ sets $\mathrm{isClosed}$ to true.

$\mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender})$ changes the round as follows:
- If $r$ is closed, or $resp$ is *not* $\mathrm{NoFresher}$ than $r.\mathrm{clusterState}$, the round is returned unchanged.
- Otherwise the list becomes $(\mathit{sender}, resp)$ followed by the old list with every entry whose sender equals $\mathit{sender}$ removed. If the votes then form an election quorum and no election was started yet, $\mathrm{electionStarted}$ becomes true.

The cluster state and the local node never change.

**Reachability.** $\mathrm{RoundReachable}_{es,\mathit{Delivered}}$ is the least predicate on rounds closed under three rules:
- every $\mathrm{start}(s, n)$ is reachable;
- if $r$ is reachable and $\mathit{Delivered}(\mathit{sender}, resp)$ holds, then for any $lr$ the round produced by $\mathrm{handlePreVoteResponse}(es, lr, r, resp, \mathit{sender})$ is reachable;
- if $r$ is reachable, so is $\mathrm{close}(r)$.

## 1. Declaration

**Binders and hypothesis.**
- $V$: an implicit type;
- $es$: an election strategy (an arbitrary Boolean "extra constraint" function);
- $\mathit{Delivered}$: an arbitrary predicate on (discovery node, response) pairs;
- $r$: a round over $V$;
- $hr$: $\mathrm{RoundReachable}_{es,\mathit{Delivered}}(r)$.

**Conclusion.** Two conjuncts:
1. For every entry $p = (\mathit{sender}, resp)$ of $r.\mathrm{preVotesReceived}$, both of these hold:
   - $\mathrm{NoFresher}(resp, r.\mathrm{clusterState})$: the response's (last accepted term, last accepted version) is lexicographically at most $(r.\mathrm{clusterState}.\mathrm{term}, \mathrm{vomv}(r.\mathrm{clusterState}))$;
   - $\mathit{Delivered}(\mathit{sender}, resp)$.
2. The list of senders $[p.1 \mid p \in r.\mathrm{preVotesReceived}]$ has no duplicates. No two entries have equal senders, that is, senders with the same id **and** the same flag.

## 2. What is not constrained

- **No duplicate senders is not no duplicate ids.** Conjunct 2 is about discovery-node values, not ids. Two entries whose senders share an id but differ in the flag are allowed, and do occur. I checked by evaluation: delivering from $\langle 5, \mathrm{true}\rangle$ and then from $\langle 5, \mathrm{false}\rangle$ keeps both entries.
- **Free parameters.** $es$ and $\mathit{Delivered}$ are arbitrary, and so is the local response $lr$ used in each step. The strategy affects only $\mathrm{electionStarted}$, which the conclusion does not mention.
- **Reference state.** $\mathrm{NoFresher}$ is measured against the round's own cluster state, which is fixed when the round starts. It is not measured against any later state of the requester.
- **Only one direction.** The theorem does not say every delivered response appears in the list. Fresher ones are dropped, closed rounds ignore deliveries, and a later delivery from the same sender replaces the earlier one. It says nothing about $\mathrm{electionStarted}$ or $\mathrm{isClosed}$.
- **Vacuity.** None. $\mathrm{start}(s, n)$ is reachable for every $s$ and $n$, with an empty list, where the conclusion is trivially true. Non-empty reachable lists exist whenever $\mathit{Delivered}$ holds for some pair whose response is $\mathrm{NoFresher}$ than $s$.

## 3. Plain-language summary

In any round obtained by starting, handling delivered responses (with any local response) and closing, every recorded pre-vote really was delivered by its sender and is no fresher than the round's accepted state. No sender, taken as an (id, role) pair, is recorded twice.
