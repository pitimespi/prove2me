# Read-back: `OpenSearchProgress.election_vote_accepted`

## Notions used

The full expansions are in `readback_Def_OpenSearchProgress.md`. This section repeats what the statement needs.

**Node-state notation.** For a node state $\sigma$:

- $\mathrm{cur}(\sigma)$ is the current term (a natural number) and $\mathrm{acc}(\sigma)$ the last accepted cluster state;
- $\mathrm{lat}(\sigma)$ and $\mathrm{lav}(\sigma)$ are that state's term and (integer) version;
- $\mathrm{lavm}(\sigma)$ is its metadata version if its term is 0, and its version otherwise;
- $\mathrm{lcc}(\sigma)$ and $\mathrm{lac}(\sigma)$ are its last committed and last accepted voting configurations;
- $\mathrm{jv}(\sigma)$ is the list of ids in the join votes, $\mathrm{sj}(\sigma)$ is `startedJoinSinceLastReboot`, $\mathrm{won}(\sigma)$ is `electionWon` and $\mathrm{lpv}(\sigma)$ is `lastPublishedVersion`.

$(a, b) \preceq (a', b')$ means $a < a' \lor (a = a' \land b \le b')$.

**Clusters and reachability.** A cluster $W$ assigns a node state $W.\mathrm{node}(n)$ to every node id, and has a set $W.\mathrm{sent}$ of messages that only ever grows. $\mathrm{Reachable}(P, W)$ means $W$ is obtained from an initial cluster by finitely many `Step`s. In an initial cluster every node $n$ is $\mathrm{init}(P.\mathrm{dn}(n), 0, s)$ with $s$ a term-0 state with empty configurations, and no message has been sent. A `Step` is one successful handler call at one node, with its output sent; the kinds are bootstrap, start-join, join, client value, publish, respond, commit, restart of an eligible node (term kept), and `restartAny` of a non-eligible node (any term, any state).

**The election period.** $\mathrm{ElectionExec}(P, c, t, Q, k_t, k_v)(W, W')$ is a finite, possibly empty, sequence of *election steps* from $W$ to $W'$. Each election step is a `Step` of one of the following kinds, where $\sigma$ is the acting node's state:

- bootstrap of a node $n \notin \{c\} \cup Q$;
- start-join at any node $n$, on a request from an eligible $src$ in term $t'$ with $t' < t \lor (src = c \land t' = t)$:
  - it succeeds iff $t' > \mathrm{cur}(\sigma)$;
  - $n$ then moves to term $t'$, with $\mathrm{sj} := \mathrm{true}$, $\mathrm{won} := \mathrm{false}$, votes cleared and $\mathrm{lpv} := 0$;
  - $n$ sends the join $\langle \mathrm{ln}(\sigma), P.\mathrm{dn}(src), t', \mathrm{lat}(\sigma), \mathrm{lavm}(\sigma)\rangle$;
- join: any node handles any sent join whose target id is that node;
- publish: any node $n$ handles any sent publication request $(src, s, pt, pv)$, provided that $(s.\mathrm{term}, s.\mathrm{version}) \preceq (k_t, k_v)$ whenever $n = c$ or $n \in Q$. The response goes to $src$;
- respond: any node handles any sent publish response addressed to it, and a resulting commit is sent;
- commit: any node handles any sent commit;
- restart of an eligible node $n \notin \{c\} \cup Q$;
- `restartAny` of a non-eligible node.

There is no client-value step, so no new publication request is sent during the period. In this theorem, $k_t = \mathrm{lat}(W.\mathrm{node}\ c)$ and $k_v = \mathrm{lav}(W.\mathrm{node}\ c)$.

**`handleJoin(es, σ, j)`** succeeds iff all of the following hold, checked in this order:

1. $j.\mathrm{term} = \mathrm{cur}(\sigma)$;
2. $\mathrm{sj}(\sigma) = \mathrm{true}$;
3. $j.\mathrm{lastAcceptedTerm} \le \mathrm{lat}(\sigma)$;
4. not ($j.\mathrm{lastAcceptedTerm} = \mathrm{lat}(\sigma)$ and $j.\mathrm{lastAcceptedVersion} > \mathrm{lavm}(\sigma)$);
5. $\mathrm{lac}(\sigma)$ is non-empty.

On success it returns $(\sigma_2, \mathit{added})$. The new join-vote list is $\mathrm{addVote}(\mathrm{jv}(\sigma), j.\mathrm{sourceNode}).1$: $j.\mathrm{sourceNode}.\mathrm{id}$ is prepended if $j.\mathrm{sourceNode}.\mathrm{isClusterManagerNode} = \mathrm{true}$ and the id is not yet present, and the list is unchanged otherwise. $\sigma_2$'s $\mathrm{won}$ is recomputed, and its $\mathrm{lpv}$ may be reset. The strategy $es$ influences only $\mathrm{won}$ and $\mathrm{lpv}$, not success and not the vote list.

## 1. Declaration

The universally quantified variables and hypotheses, in order:

| Name | Type / statement |
|---|---|
| `V` (implicit) | `Type`: the payload type |
| `P` | `Params` |
| `hP` | $P.\mathrm{InitCompatible}$: for bootstrap configurations $X, Y$ and lists $q_1, q_2$ of eligible ids, $\mathrm{Quorum}(X, q_1) \land \mathrm{Quorum}(Y, q_2) \to q_1 \cap q_2 \ne \emptyset$ |
| `hes` | $P.\mathrm{strategy} = \mathrm{DEFAULT\_INSTANCE}$ (no additional quorum constraint) |
| `W` | `Cluster V`: the cluster at the start of the period |
| `hW` | $\mathrm{Reachable}(P, W)$ |
| `c` | node id: the candidate |
| `t` | $\mathbb{N}$: the election term |
| `Q` | list of node ids: the voters |
| `hc` | $P.\mathrm{eligible}(c) = \mathrm{true}$ |
| `hQ` | $\forall q \in Q,\ P.\mathrm{eligible}(q) = \mathrm{true}$ |
| `hterm` | $\forall q,\ (q = c \lor q \in Q) \to \mathrm{cur}(W.\mathrm{node}\ q) < t$ |
| `hfresh` | $\forall q \in Q,\ \mathrm{lat}(W.\mathrm{node}\ q) < \mathrm{lat}(W.\mathrm{node}\ c) \lor \big(\mathrm{lat}(W.\mathrm{node}\ q) = \mathrm{lat}(W.\mathrm{node}\ c) \land \mathrm{lavm}(W.\mathrm{node}\ q) \le \mathrm{lavm}(W.\mathrm{node}\ c)\big)$ |
| `hconf` | $\mathrm{lac}(W.\mathrm{node}\ c)$ is non-empty (`isEmpty = false`) |
| `W'` | `Cluster V` |
| `hE` | $\mathrm{ElectionExec}(P, c, t, Q, \mathrm{lat}(W.\mathrm{node}\ c), \mathrm{lav}(W.\mathrm{node}\ c))(W, W')$ |
| `hct` | $\mathrm{cur}(W'.\mathrm{node}\ c) = t$ |
| `j` | `Join` |
| `hj` | $\mathrm{join}(j) \in W'.\mathrm{sent}$ |
| `hsrc` | $j.\mathrm{sourceNode}.\mathrm{id} \in Q$ |
| `htgt` | $j.\mathrm{targetNode}.\mathrm{id} = c$ |
| `hjt` | $j.\mathrm{term} = t$ |

**Conclusion.**
$$\exists\, cs'\ b,\quad \mathrm{handleJoin}(P.\mathrm{strategy}, W'.\mathrm{node}\ c, j) = \mathrm{ok}(cs', b) \;\land\; j.\mathrm{sourceNode}.\mathrm{id} \in cs'.\mathrm{joinVotes}.\mathrm{nodes}.$$

**Unfolded.** Write $\sigma' = W'.\mathrm{node}\ c$. The conclusion says that all five guards of `handleJoin` pass at $\sigma'$ for $j$, and that the source's id is in the resulting vote list. Guard 1 ($j.\mathrm{term} = \mathrm{cur}(\sigma')$) follows directly from `hjt` and `hct`. The remaining content is:

- (ii) $\mathrm{sj}(\sigma') = \mathrm{true}$;
- (iii) $j.\mathrm{lastAcceptedTerm} \le \mathrm{lat}(\sigma')$;
- (iv) $j.\mathrm{lastAcceptedTerm} = \mathrm{lat}(\sigma') \to j.\mathrm{lastAcceptedVersion} \le \mathrm{lavm}(\sigma')$;
- (v) $\mathrm{lac}(\sigma')$ is non-empty;
- (vi) $j.\mathrm{sourceNode}.\mathrm{isClusterManagerNode} = \mathrm{true}$, or $j.\mathrm{sourceNode}.\mathrm{id} \in \mathrm{jv}(\sigma')$ already.

$cs'$ is then determined as the handler's output, and $b$ records whether the vote was new. Nothing is claimed about $cs'.\mathrm{electionWon}$, $cs'.\mathrm{lastPublishedVersion}$ or $b$.

In words: at the end of any stable election period in which $c$ has reached term $t$, every term-$t$ join that a voter has addressed to $c$ can be handled by $c$ without rejection, and handling it records that voter's vote.

## 2. What is not constrained

- **$Q$.**
  - It is not required to be a quorum of anything; this theorem has no quorum hypothesis.
  - It may contain $c$. `hfresh` is then trivial for $q = c$, and $j$ may be $c$'s own join to itself.
  - It may contain duplicates, or nodes outside $c$'s configurations.
  - If $Q = [\,]$, `hsrc` cannot hold and the statement is vacuous. That is the only degenerate case.
- **Other nodes.** Nodes outside $\{c\} \cup Q$ are unconstrained at $W$: any term (even $\ge t$), any accepted state, possibly elected in some term. The period allows them every step except start-joins to terms $\ge t$ other than $c$'s request for $t$, and new publications.
- **The join $j$.** Only its source id, target id and term are constrained. Its $\mathrm{lastAcceptedTerm}$ and $\mathrm{lastAcceptedVersion}$, and its source node's cluster-manager flag, are not hypotheses. So claims (iii), (iv) and (vi) assert facts about whichever term-$t$ joins from voters to $c$ can exist in $W'$. The target node's flag is not constrained either, only its id.

  The following is derived by me, not stated. In a reachable cluster, the joins a voter has produced by $W$ have terms $\le$ its current term $< t$. So $j$ was produced during the period, by the voter handling $c$'s request for $t$; in the period, term $t$ can only be entered on $c$'s request. Its source node is $P.\mathrm{dn}(q)$, which is flagged cluster-manager because $q$ is eligible.
- **Whether $j$ was already handled.** $c$ may already have handled $j$ during the period. The claim is that handling it (again) at $W'$ succeeds and leaves the vote present. The statement is about the pure handler applied to $W'.\mathrm{node}\ c$, not about a step. Since the period does not restrict join steps, and $j$ is sent with target id $c$, the handler's success is exactly what an election join step from $W'$ needs.
- **Freshness.** `hfresh` compares voters with $c$ using $\mathrm{lavm}$, exactly `handleJoin`'s measure, but only at $W$. The period's freshness bound $(k_t, k_v)$ uses $\mathrm{lav}$ (version) instead. The two coincide for $c$ when $\mathrm{lat}(W.\mathrm{node}\ c) \ge 1$. When $\mathrm{lat}(W.\mathrm{node}\ c) = 0$, the period lets $c$ and the voters accept no publication at all (no term-0 publication exists in a reachable cluster), so the voters' metadata versions cannot move. The theorem thus implicitly claims that the start-of-period comparison survives every stable period, including voters' acceptances of publications whose key is $\preceq (k_t, k_v)$.
- **$c$'s configurations.** Only `hconf` ($\mathrm{lac}$ non-empty at $W$) is assumed. Nothing is assumed about $\mathrm{lcc}(W.\mathrm{node}\ c)$, and nothing links $c$'s configurations to $Q$. Claim (v) is about $W'$.
- **`hes`, `hP`.** These are global assumptions on $P$. The conclusion's form does not depend on the strategy, which affects only $cs'.\mathrm{won}$ and $cs'.\mathrm{lpv}$; neither is mentioned.
- **Empty execution.** `hterm` with `hct` forces $t \ge 1$ and rules out the empty execution: $\mathrm{cur}(W.\mathrm{node}\ c) < t = \mathrm{cur}(W'.\mathrm{node}\ c)$, so at least $c$'s start-join into $t$ occurs, on a request whose requester is $c$.
- **Vacuity.** The hypotheses are jointly satisfiable. Example:
  - eligible nodes 1 and 2;
  - $P.\mathrm{initConfs}(X) \iff X = \{1, 2\}$. `InitCompatible` holds, because every quorum of $\{1, 2\}$ contains both nodes;
  - the default strategy;
  - both nodes bootstrapped, from an initial cluster, with the same term-0 state: version 0, metadata version 0, configurations $\{1, 2\}$;
  - $c = 1$, $Q = [2]$, $t = 1$.

  In the period, node 1 start-joins on its own request for term 1, and node 2 start-joins on node 1's request for term 1, sending $j = \langle P.\mathrm{dn}\ 2, P.\mathrm{dn}\ 1, 1, 0, 0\rangle$. Every hypothesis holds at $W'$, and the conclusion is a real claim.

## 3. Plain-language summary

Start from any reachable cluster in which:

- the candidate $c$ and the voters $Q$ are eligible and in terms below $t$;
- $c$ has a non-empty accepted configuration;
- no voter's last accepted state is fresher than $c$'s, in `handleJoin`'s comparison.

Then run any stable election period: no start-join anywhere to a term $\ge t$ except on $c$'s request for $t$, no new publications, no restarts or bootstraps of $c$ or of voters, and $c$ and the voters accept nothing fresher than $c$'s starting state. If $c$ has reached term $t$, then $c$ can accept any term-$t$ join that a voter has sent it, and accepting it records the voter's vote. The theorem does not claim that a voter's join is ever sent, nor that $c$ wins.
