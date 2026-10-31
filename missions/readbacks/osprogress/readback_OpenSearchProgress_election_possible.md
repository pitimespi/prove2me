# Read-back: `OpenSearchProgress.election_possible`

## Notions used

The full expansions are in `readback_Def_OpenSearchProgress.md`.

**Node-state notation.** For a node state $\sigma$:

- $\mathrm{cur}(\sigma)$ is the current term;
- $\mathrm{lat}(\sigma)$ and $\mathrm{lav}(\sigma)$ are the term and version of the last accepted state;
- $\mathrm{lavm}(\sigma)$ is that state's metadata version if its term is 0, and its version otherwise;
- $\mathrm{lcc}(\sigma)$ and $\mathrm{lac}(\sigma)$ are its last committed and last accepted configurations;
- $\mathrm{won}(\sigma)$ is `electionWon`.

$\mathrm{Quorum}(X, L)$ means that strictly more than half of the ids of configuration $X$ occur in the list $L$. It is false for an empty $X$ and for $L = [\,]$.

**The election period** $\mathrm{ElectionExec}(P, c, t, Q, k_t, k_v)(W, W')$ is a finite, possibly empty, sequence of `Step`s from $W$ to $W'$, each of one of the following kinds. Here $\sigma$ is the acting node's state.

- **bootstrap** of a node outside $\{c\} \cup Q$.
- **start-join** at any node $n$, on a request from an eligible $src$ in term $t'$, where $t' < t$ or ($src = c$ and $t' = t$). It succeeds iff $t' > \mathrm{cur}(\sigma)$. The node then moves to term $t'$ (clearing votes, setting `startedJoinSinceLastReboot` and resetting `electionWon`) and sends the join $\langle \mathrm{ln}(\sigma), P.\mathrm{dn}(src), t', \mathrm{lat}(\sigma), \mathrm{lavm}(\sigma)\rangle$.
- **join**: a node handles a sent join addressed to it. `handleJoin` succeeds iff:
  - the term matches;
  - the node has started a join since its last restart;
  - the join's last accepted (term, version) is not above the node's $(\mathrm{lat}, \mathrm{lavm})$ in the order "term first, then version within the same term";
  - the node's $\mathrm{lac}$ is non-empty.

  It then adds the source's id, if the source is flagged cluster-manager, and recomputes `electionWon`. Under the default strategy the new value is "votes are a quorum of both $\mathrm{lcc}$ and $\mathrm{lac}$".
- **publish**: any node handles any sent publication, except that $c$ and members of $Q$ may accept only publications with key $\preceq (k_t, k_v)$.
- **respond** and **commit**: unrestricted.
- **restart** of an eligible node outside $\{c\} \cup Q$.
- **restartAny** of a non-eligible node.

There is no step that sends a new publication. In this theorem, $(k_t, k_v) = (\mathrm{lat}, \mathrm{lav})$ of $W.\mathrm{node}\ c$.

## 1. Declaration

The universally quantified variables and hypotheses, in order:

| Name | Type / statement |
|---|---|
| `V` (implicit) | `Type` |
| `P` | `Params` |
| `hP` | $P.\mathrm{InitCompatible}$ |
| `hes` | $P.\mathrm{strategy} = \mathrm{DEFAULT\_INSTANCE}$ |
| `W` | `Cluster V` |
| `hW` | $\mathrm{Reachable}(P, W)$ |
| `c` | node id (candidate) |
| `t` | $\mathbb{N}$ (election term) |
| `Q` | list of node ids (voters) |
| `hc` | $P.\mathrm{eligible}(c) = \mathrm{true}$ |
| `hQ` | $\forall q \in Q,\ P.\mathrm{eligible}(q) = \mathrm{true}$ |
| `hquorum` | $\mathrm{Quorum}(\mathrm{lcc}(W.\mathrm{node}\ c), Q) \land \mathrm{Quorum}(\mathrm{lac}(W.\mathrm{node}\ c), Q)$ |
| `hterm` | $\forall q,\ (q = c \lor q \in Q) \to \mathrm{cur}(W.\mathrm{node}\ q) < t$ |
| `hfresh` | $\forall q \in Q,\ \mathrm{lat}(W.\mathrm{node}\ q) < \mathrm{lat}(W.\mathrm{node}\ c) \lor \big(\mathrm{lat}(W.\mathrm{node}\ q) = \mathrm{lat}(W.\mathrm{node}\ c) \land \mathrm{lavm}(W.\mathrm{node}\ q) \le \mathrm{lavm}(W.\mathrm{node}\ c)\big)$ |

**Conclusion.**
$$\exists\, W',\quad \mathrm{ElectionExec}(P, c, t, Q, \mathrm{lat}(W.\mathrm{node}\ c), \mathrm{lav}(W.\mathrm{node}\ c))(W, W') \;\land\; \mathrm{cur}(W'.\mathrm{node}\ c) = t \;\land\; \mathrm{won}(W'.\mathrm{node}\ c) = \mathrm{true}.$$

In words: from $W$ there is at least one stable election period for $c$, $t$ and $Q$ at whose end $c$ is in term $t$ and has won. Since $\mathrm{cur}(W.\mathrm{node}\ c) < t$, such a period contains at least $c$'s start-join into $t$, which is on a request whose requester is $c$; the guard of the period requires this. It also contains at least one successful `handleJoin` at $c$ after that start-join.

## 2. What is not constrained

- **Existence only.** The theorem asserts that *some* stable election period leads to $c$'s victory. It does not say that every period does, or that one must. It says nothing about which steps are used, how many, in what order, or what other nodes do along the way.
- **Model-relative.** The existential ranges over executions of the model. In the model, a start-join needs no `StartJoinRequest` message: any node may act on a request "from" any eligible node. The `Coordinator`'s own guards are not modelled. The witness execution may therefore use any steps the period admits. For example, a voter may join $c$'s term before $c$ itself does.
- **No `hconf` hypothesis.** `hquorum` implies $\mathrm{lac}(W.\mathrm{node}\ c)$ and $\mathrm{lcc}(W.\mathrm{node}\ c)$ are non-empty, and that $Q \ne [\,]$.
- **`hfresh` is the right measure, at $W$ only.** `hfresh` uses $\mathrm{lavm}$, exactly the measure that `handleJoin` compares, and it holds at $W$. The period's freshness bound uses $\mathrm{lav}$. The witness may use only steps that keep the voters' joins acceptable.
- **`hc` is needed.** A start-join's requester must be eligible, and the period lets term $t$ be entered only on a request whose requester is $c$.
- **Other nodes are unconstrained.** Nodes outside $\{c\} \cup Q$ are unconstrained at $W$: any term, possibly $\ge t$, possibly elected in some other term.
- **Implicit claim about other winners.** The conclusion makes $c$ a winner of term $t$ in a cluster reachable from $W$; every election step is a `Step`. The Safety definitions' invariant field `Inv.won_unique` says at most one node wins each term. So the theorem implicitly asserts that its hypotheses exclude a $W$ in which another node has already won term $t$, or has published in it. No hypothesis says so directly. It would have to follow from `hquorum`, `hterm` (no voter has reached $t$), `hfresh` and reachability.
- **Vacuity.** The hypotheses are satisfiable. Take eligible nodes 1 and 2, bootstrap configuration $\{1, 2\}$ only, and the default strategy. Bootstrap both nodes with the same term-0 state (version 0, metadata version 0). Set $c = 1$, $Q = [1, 2]$, $t = 1$. A witness period:
  1. node 1 start-joins on its own request for term 1;
  2. node 2 start-joins on node 1's request;
  3. node 1 handles both joins and wins.

## 3. Plain-language summary

Suppose a reachable cluster under the default strategy satisfies:

- the eligible candidate $c$ and the eligible voters $Q$ are all below term $t$;
- $Q$ is a majority of both of $c$'s configurations;
- no voter's last accepted state is fresher than $c$'s.

Then the model has a stable election period, with no competing elections and no new publications, at the end of which $c$ is in term $t$ and has won. It is an existence result. Together with `election_vote_accepted` and `election_won` it describes possible progress; it does not claim that progress is inevitable.
