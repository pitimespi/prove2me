# Read-back: `OpenSearchProgress.publication_committed`

## Notions used

The full expansions are in `readback_Def_OpenSearchProgress.md`.

**Node-state notation.** For a node state $\sigma$:

- $\mathrm{cur}(\sigma)$ is the current term;
- $\mathrm{lcc}(\sigma)$ and $\mathrm{lac}(\sigma)$ are the last committed and last accepted configurations of its accepted state;
- $\mathrm{lpc}(\sigma)$ is `lastPublishedConfiguration`;
- $\mathrm{won}(\sigma)$ is `electionWon`;
- $\mathrm{lpv}(\sigma)$ is `lastPublishedVersion`;
- $\mathrm{pv}(\sigma)$ is the list of ids in the publish votes.

For a cluster state $s$, $s.\mathrm{lcc}$ and $s.\mathrm{lac}$ are its two configurations. $\mathrm{Quorum}(X, L)$ means strictly more than half of the ids of configuration $X$ occur in the list $L$. It is false for an empty $X$ and for $L = [\,]$, and it is monotone in $L$.

**The publication period** $\mathrm{PublicationExec}(P, c, t, Q)(W, W')$ is a finite, possibly empty, sequence of `Step`s from $W$ to $W'$. Compared with arbitrary steps, the period imposes exactly three restrictions:

- no start-join at $c$ or at a member of $Q$ to a term above $t$;
- no new publication (`clientValue`) by $c$;
- no `restart` of $c$.

Everything else is allowed: bootstraps, other nodes' start-joins and publications, every join, publish, respond and commit step, restarts of members of $Q$, and `restartAny` of non-eligible nodes.

**How publish votes and commits arise.** Publish votes are cleared by `handleClientValue`, `handleStartJoin` and restarts, and grow only in `handlePublishResponse`. That handler requires $\mathrm{won}$, a matching term, and a version equal to $\mathrm{lpv}$. It adds the responder's id if the responder is flagged cluster-manager. If the new votes $v'$ satisfy $\mathrm{Quorum}(\mathrm{lcc}(\sigma), v') \land \mathrm{Quorum}(\mathrm{lpc}(\sigma), v')$, it returns an apply-commit request $\langle \mathrm{ln}(\sigma), \tau, v\rangle$, which the respond step sends.

**Committed.** $\mathrm{Committed}(W, \tau, v)$ means some apply-commit request $\langle d, \tau, v\rangle$, from any source $d$, is in $W.\mathrm{sent}$.

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
| `hpv` | $\mathrm{pv}(W.\mathrm{node}\ c) = [\,]$ |
| `W'` | `Cluster V` |
| `hE` | $\mathrm{PublicationExec}(P, c, t, Q)(W, W')$ |
| `hacks` | $\forall q \in Q,\ q \in \mathrm{pv}(W'.\mathrm{node}\ c)$ |

**Conclusion.** $\mathrm{Committed}(W', t, s.\mathrm{version})$, that is,
$$\exists\, d,\ \mathrm{applyCommit}\langle d, t, s.\mathrm{version}\rangle \in W'.\mathrm{sent}.$$

In words: if $c$ starts the period holding no publish votes and ends it holding publish votes from every member of $Q$, then an apply-commit request for term $t$ and version $s.\mathrm{version}$ has been sent by some node.

## 2. What is not constrained

- **`hpv` narrows the start of the period.** The period must start while $c$ holds no publish votes, for example right after $c$ published $s$ and before it counted any acknowledgement from an eligible node. A period starting after some acknowledgements have been counted is not covered by this statement as written.
- **Every member of $Q$ must have acknowledged.** `hacks` requires every member of $Q$ to be among $c$'s publish votes at $W'$, not just a quorum's worth. It does not say directly that the votes acknowledge $s$. Publish votes are added only when an acknowledgement's version equals $\mathrm{lpv}(c)$, and $c$ cannot publish again during the period.
- **Four configurations.** `hquorum` requires $Q$ to be a majority of four configurations: $c$'s last committed and last accepted configurations at $W$, and $s$'s two configurations. It thereby forces $Q \ne [\,]$ and all four configurations non-empty. Which configurations $c$ compares against when it counts the last vote ($\mathrm{lcc}(c)$ at that moment, and $\mathrm{lpc}(c)$) is not stated. The theorem implicitly claims they are among those covered.
- **Model-relative.** In the model, the commit is sent as soon as the counted votes form a quorum. In Java, `handlePreCommit()`, the remote-store write at `CoordinationState.java:510`, runs first and may throw. The Coordination file abstracts this away; see G5 in the definitions read-back.
- **The conclusion is weak.** It says only that a commit has been *sent*. It does not say that any node, $c$ included, has applied it. The source $d$ of the commit is existential.
- **No term hypothesis on $Q$.** Members of $Q$ may be in any term at $W$.
- **Implicit reliance on $c$'s flags.** This is derived by me, not stated.
  - During the period, $c$'s publish votes are never cleared: $c$ cannot publish, cannot start-join (it is in term $t$ and the period forbids terms above $t$), and cannot be restarted.
  - So they reach $Q$ through successful `handlePublishResponse` calls, and the last of these returns the commit if $c$'s configurations at that moment are covered.
  - That commit carries the version $\mathrm{lpv}(c)$ at that moment. The conclusion therefore needs $\mathrm{lpv}(c)$ still to be $s.\mathrm{version}$.
  - Within the period, $\mathrm{lpv}(c)$ can change only through `handleJoin`'s "newly won" branch, which sets $\mathrm{lpv} := \mathrm{lav}$ when $\mathrm{won}$ goes from false to true. That branch requires $c$ to have lost `electionWon` first. The Lean `handleJoin` does not exclude losing it; Java only asserts that it cannot happen (CS:323).

  So the theorem relies on this being impossible, or harmless, in reachable clusters under the default strategy (`hes`).
- **$c$'s eligibility.** It is not assumed. It follows from `hwon` in a reachable cluster, because only eligible nodes receive joins.
- **Empty execution.** It is excluded. With $W' = W$, `hacks` and `hpv` would force $Q = [\,]$, contradicting `hquorum`. So at least one respond step at $c$ occurs in the period.
- **Vacuity.** The hypotheses are satisfiable. Single-node example:
  1. Node 1 is eligible, the bootstrap configuration is $\{1\}$ only, and the strategy is the default.
  2. Node 1 bootstraps, start-joins on its own request for term 1, handles its own join (and wins), and publishes $s$ (term 1, version 1, both configurations $\{1\}$). Publishing clears its publish votes. $W$ is the cluster at this point, with $c = 1$, $t = 1$, $Q = [1]$.
  3. In the period, node 1 accepts its own publication, sending itself the acknowledgement $\langle 1, 1\rangle$, then counts it. Its votes $[1]$ are a quorum of $\{1\}$, so the commit $\langle P.\mathrm{dn}\ 1, 1, 1\rangle$ is sent.

## 3. Plain-language summary

Suppose that, in a reachable cluster under the default strategy:

- $c$ has won term $t$ and has just sent $s$ as its latest publication;
- $c$ has not yet counted any acknowledgement;
- $Q$ is a majority of $c$'s configurations and of $s$'s configurations.

If, during a stable publication period, $c$ comes to hold acknowledgements from every member of $Q$, then a commit for $(t, s.\mathrm{version})$ has been sent. It is the "the acknowledgements suffice" half of publication progress. It assumes the acknowledgements rather than deriving them, and it claims only that the commit was sent, not that it was applied.
