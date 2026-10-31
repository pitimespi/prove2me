# Read-back: `OpenSearchProgress.election_won`

## Notions used

The full expansions are in `readback_Def_OpenSearchProgress.md`.

**Node-state notation.** For a node state $\sigma$:

- $\mathrm{cur}(\sigma)$ is the current term;
- $\mathrm{lat}(\sigma)$ and $\mathrm{lav}(\sigma)$ are the term and version of its last accepted state;
- $\mathrm{lcc}(\sigma)$ and $\mathrm{lac}(\sigma)$ are that state's last committed and last accepted configurations;
- $\mathrm{jv}(\sigma)$ is the list of ids in the join votes, and $\mathrm{won}(\sigma)$ is `electionWon`.

For a configuration $X$ (a strictly increasing list of ids) and a list $L$ of ids, $\mathrm{Quorum}(X, L)$ (`X.hasQuorum L = true`) means $2\cdot|\{x \in X : x \in L\}| > |X|$. It is false when $X$ is empty or $L = [\,]$, and it is monotone in $L$.

**Reachable clusters and the election period.** These are as in the read-back of `election_vote_accepted`. $\mathrm{ElectionExec}(P, c, t, Q, k_t, k_v)(W, W')$ is a finite, possibly empty, sequence of `Step`s. Compared with an arbitrary `Step`, the period imposes these restrictions:

- no new publication request is sent;
- a start-join at any node on a request in term $t'$ requires $t' < t$, or requester $c$ and $t' = t$;
- $c$ and the voters do not bootstrap and are not restarted, except that a non-eligible node may `restartAny`;
- $c$ and the voters accept only publications with key $\preceq (k_t, k_v)$.

In this theorem, $(k_t, k_v) = (\mathrm{lat}, \mathrm{lav})$ of $W.\mathrm{node}\ c$.

**How `electionWon` changes.** Each successful `handleJoin` sets it to $\mathrm{isElectionQuorum}(P.\mathrm{strategy}, \sigma, v)$, where $v$ is the new vote list. Under the default strategy that value is $\mathrm{Quorum}(\mathrm{lcc}(\sigma), v) \land \mathrm{Quorum}(\mathrm{lac}(\sigma), v)$, computed with the node's configurations at that moment. `handleStartJoin` and both kinds of restart set it to false. No other handler changes it. Join votes are cleared by `handleStartJoin` and by restarts, and grow only through `handleJoin`.

## 1. Declaration

The universally quantified variables and hypotheses, in order:

| Name | Type / statement |
|---|---|
| `V` (implicit) | `Type` |
| `P` | `Params` |
| `hP` | $P.\mathrm{InitCompatible}$ |
| `hes` | $P.\mathrm{strategy} = \mathrm{DEFAULT\_INSTANCE}$ |
| `W` | `Cluster V` (start of the period) |
| `hW` | $\mathrm{Reachable}(P, W)$ |
| `c` | node id (candidate) |
| `t` | $\mathbb{N}$ (election term) |
| `Q` | list of node ids (voters) |
| `hc` | $P.\mathrm{eligible}(c) = \mathrm{true}$ |
| `hQ` | $\forall q \in Q,\ P.\mathrm{eligible}(q) = \mathrm{true}$ |
| `hquorum` | $\mathrm{Quorum}(\mathrm{lcc}(W.\mathrm{node}\ c), Q) \land \mathrm{Quorum}(\mathrm{lac}(W.\mathrm{node}\ c), Q)$ |
| `hterm` | $\forall q,\ (q = c \lor q \in Q) \to \mathrm{cur}(W.\mathrm{node}\ q) < t$ |
| `W'` | `Cluster V` |
| `hE` | $\mathrm{ElectionExec}(P, c, t, Q, \mathrm{lat}(W.\mathrm{node}\ c), \mathrm{lav}(W.\mathrm{node}\ c))(W, W')$ |
| `hct` | $\mathrm{cur}(W'.\mathrm{node}\ c) = t$ |
| `hvotes` | $\forall q \in Q,\ q \in \mathrm{jv}(W'.\mathrm{node}\ c)$ |

**Conclusion.** $\mathrm{won}(W'.\mathrm{node}\ c) = \mathrm{true}$.

**What this amounts to.** `hterm` and `hct` together show that $c$ entered term $t$ during the period, by a start-join that cleared its votes and set $\mathrm{won} := \mathrm{false}$. $c$ cannot be restarted during the period, so the flag at $W'$ is the value computed by the last successful `handleJoin` at $c$ after that start-join; such a call exists because `hvotes` and $Q \ne [\,]$ make the vote list non-empty. The theorem asserts that this value is true. The hypothesis `hquorum` refers to $c$'s configurations at the start $W$. The hypothesis `hvotes` refers to $c$'s join votes at the end $W'$.

## 2. What is not constrained

- **Non-emptiness.** `hquorum` forces $Q \ne [\,]$ and both of $c$'s configurations at $W$ to be non-empty, since $\mathrm{Quorum}$ is false for an empty configuration and for an empty list.
- **No freshness or `hconf`.** There is no freshness hypothesis and no `hconf`. Whether voters' joins could be accepted does not matter here, because `hvotes` assumes the votes are present. The theorem does not derive the votes.
- **Every member of $Q$ must have voted.** `hvotes` requires every member of $Q$ to be among $c$'s join votes, not merely a quorum's worth, so members of $Q$ outside $c$'s configurations must also have voted. Since $Q$ can be chosen as a minimal quorum, this concerns how the theorem is applied, not its content. $c$'s votes may also include nodes outside $Q$.
- **Start configurations versus end configurations.** `hquorum` speaks of $c$'s configurations at $W$, not at $W'$. The following is derived, not stated:
  - during the period $c$ accepts no publication, so $\mathrm{lac}(c)$ is fixed;
  - a commit at $c$ while $c$ is still in its old term can replace $\mathrm{lcc}(c)$ by $\mathrm{lac}(c)$, which `hquorum`'s second conjunct covers;
  - once $c$ is in term $t$, no commit can apply at $c$, because $\mathrm{lat}(c) < t$.

  The theorem thus implicitly claims that $c$'s configurations, at the moment it computes its last `won` flag, are still covered by $Q$.
- **Nothing beyond the flag.** The theorem says nothing about how the votes were obtained, about $\mathrm{lpv}$ or publish votes, or about other nodes. Those may be in any term, including $\ge t$, at $W$.
- **Implicit claim about other winners.** The conclusion makes $c$ a winner of term $t$ in a reachable cluster. The Safety definitions' invariant field `Inv.won_unique` says at most one node wins each term. So the theorem implicitly asserts that its hypotheses exclude another node having won term $t$ before or during the period. No hypothesis says so directly; it would have to follow from `hquorum`, `hterm` (no voter is in term $t$ at $W$), `hvotes` and reachability.
- **Empty execution.** `hterm` and `hct` exclude the empty execution and force $t \ge 1$.
- **Vacuity.** The hypotheses are satisfiable, using the two-node example of the `election_vote_accepted` read-back with $Q = [1, 2]$ and $c = 1$, $t = 1$:
  1. node 1 start-joins on its own request for term 1, sending a join to itself;
  2. node 2 start-joins on node 1's request;
  3. node 1 handles its own join, giving votes $[1]$, not yet a quorum of $\{1, 2\}$;
  4. node 1 handles node 2's join, giving votes $[2, 1]$.

  Then `hvotes` holds, `hquorum` holds ($\{1, 2\}$ is a quorum of $\{1, 2\}$), and the conclusion is a real claim.

## 3. Plain-language summary

Take any stable election period that starts in a reachable cluster where:

- the eligible candidate $c$ and the voters $Q$ are in terms below $t$;
- $Q$ is a majority of both of $c$'s configurations, under the default election strategy.

If $c$ ends the period in term $t$ holding join votes from every member of $Q$, then $c$'s `electionWon` flag is set. This is the "the votes suffice" half of election progress. It assumes the votes rather than deriving them.
