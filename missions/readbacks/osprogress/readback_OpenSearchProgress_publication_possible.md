# Read-back: `OpenSearchProgress.publication_possible`

## Notions used

The full expansions are in `readback_Def_OpenSearchProgress.md`.

**Node-state notation.** For a node state $\sigma$:

- $\mathrm{cur}(\sigma)$ is the current term;
- $\mathrm{lcc}(\sigma)$ and $\mathrm{lac}(\sigma)$ are the configurations of its accepted state;
- $\mathrm{won}(\sigma)$ is `electionWon`;
- $\mathrm{lpv}(\sigma)$ is `lastPublishedVersion`.

For a cluster state $s$, $s.\mathrm{lcc}$ and $s.\mathrm{lac}$ are its two configurations. $\mathrm{Quorum}(X, L)$ means that strictly more than half of the ids of configuration $X$ occur in the list $L$.

**The publication period.** $\mathrm{PublicationExec}(P, c, t, Q)(W, W')$ is a finite, possibly empty, sequence of `Step`s. Compared with arbitrary steps, it imposes exactly three restrictions:

- no start-join at $c$ or at a member of $Q$ to a term above $t$;
- no new publication by $c$;
- no `restart` of $c$.

Everything else is allowed. That includes start-joins at members of $Q$ to terms $\le t$, on a request from any eligible node. A start-join requires no message: it is a spontaneous step of the model.

**The handlers involved.**

- `handlePublishRequest` accepts $s$ at a node in term $s.\mathrm{term}$, unless the node has already accepted a state of the same term with version $\ge s.\mathrm{version}$. The acceptance is answered by a publish response to the publisher.
- `handlePublishResponse` at an elected node, for its current term and its last published version, adds the responder's vote. It sends an apply-commit request when the votes are a quorum of the node's last committed and last published configurations.

**Committed.** $\mathrm{Committed}(W, \tau, v)$ means some apply-commit request $\langle d, \tau, v\rangle$, from any source $d$, has been sent in $W$.

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
| `c` | node id (the cluster-manager) |
| `t` | $\mathbb{N}$ |
| `Q` | list of node ids (acknowledging nodes) |
| `hQ` | $\forall q \in Q,\ P.\mathrm{eligible}(q) = \mathrm{true}$ |
| `hwon` | $\mathrm{won}(W.\mathrm{node}\ c) = \mathrm{true}$ |
| `hct` | $\mathrm{cur}(W.\mathrm{node}\ c) = t$ |
| `s` | `ClusterState V` |
| `pt` | $\mathbb{N}$ |
| `pv` | $\mathbb{Z}$ |
| `hs` | $\mathrm{publishRequest}(c, s, pt, pv) \in W.\mathrm{sent}$ |
| `hst` | $s.\mathrm{term} = t$ |
| `hsv` | $s.\mathrm{version} = \mathrm{lpv}(W.\mathrm{node}\ c)$ |
| `hquorum` | $\mathrm{Quorum}(\mathrm{lcc}(W.\mathrm{node}\ c), Q) \land \mathrm{Quorum}(\mathrm{lac}(W.\mathrm{node}\ c), Q) \land \mathrm{Quorum}(s.\mathrm{lcc}, Q) \land \mathrm{Quorum}(s.\mathrm{lac}, Q)$ |
| `hterm` | $\forall q \in Q,\ \mathrm{cur}(W.\mathrm{node}\ q) \le t$ |

**Conclusion.**
$$\exists\, W',\quad \mathrm{PublicationExec}(P, c, t, Q)(W, W') \;\land\; \exists\, d,\ \mathrm{applyCommit}\langle d, t, s.\mathrm{version}\rangle \in W'.\mathrm{sent}.$$

In words: from $W$ there is at least one stable publication period at whose end a commit for $(t, s.\mathrm{version})$ has been sent.

## 2. What is not constrained

- **Existence only.** The theorem asserts that *some* stable publication period ends with the commit sent. It does not say that every period does, or that one must. It also does not bound or describe the steps.
- **Trivial witness.** If $\mathrm{Committed}(W, t, s.\mathrm{version})$ already holds, the empty execution $W' = W$ is a witness, and the theorem is trivial for that $W$.
- **No `hpv`.** Unlike `publication_committed`, there is no hypothesis about $c$'s publish votes at $W$.
- **`hterm` allows members of $Q$ at term $\le t$.** They may be exactly in term $t$, possibly having already accepted or acknowledged $s$, or below $t$. Members above $t$ are excluded, and they could never acknowledge $s$. Members below $t$ can be moved into $t$ by a start-join, on a request from any eligible node; the period allows $t' \le t$ for them.
- **Model-relative.** The existential ranges over executions of the model. The model's start-joins need no `StartJoinRequest` message, and the `Coordinator`'s own guards are not modelled. So a member of $Q$ may move to term $t$ "spontaneously". In OpenSearch this corresponds to joining $c$ on receipt of its message.
- **$c$'s eligibility.** It is not assumed. It follows from `hwon` in a reachable cluster, because only eligible nodes receive joins.
- **Four configurations.** `hquorum` covers $c$'s two configurations at $W$ and $s$'s two configurations. It forces $Q \ne [\,]$.
- **Other nodes.** The theorem says nothing about nodes outside $Q \cup \{c\}$. They may be in higher terms, elected, or publishing, both at $W$ and along the witness.
- **Vacuity.** The hypotheses are satisfiable. Use the single-node example of the `publication_committed` read-back:
  1. node 1 bootstraps with configuration $\{1\}$, wins term 1, and publishes $s$ (term 1, version 1);
  2. take $W$ right after the publication, with $c = 1$, $t = 1$, $Q = [1]$;
  3. a witness period: node 1 accepts its own publication, then counts its own acknowledgement, which sends the commit.

## 3. Plain-language summary

Suppose that, in a reachable cluster under the default strategy:

- $c$ has won term $t$ and has sent $s$ as its latest publication;
- $Q$ is a set of eligible nodes, none above term $t$, forming a majority of $c$'s configurations and of $s$'s configurations.

Then the model has a stable publication period, in which no node of $\{c\} \cup Q$ moves above $t$ and $c$ neither publishes again nor restarts, at the end of which a commit for $(t, s.\mathrm{version})$ has been sent. It is an existence result. Together with `publication_acks_accepted` and `publication_committed` it describes possible progress; it does not claim that progress is inevitable.
