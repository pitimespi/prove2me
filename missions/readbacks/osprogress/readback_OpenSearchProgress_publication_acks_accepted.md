# Read-back: `OpenSearchProgress.publication_acks_accepted`

## Notions used

The full expansions are in `readback_Def_OpenSearchProgress.md`.

**Node-state notation.** For a node state $\sigma$:

- $\mathrm{cur}(\sigma)$ is the current term;
- $\mathrm{lat}(\sigma)$ and $\mathrm{lav}(\sigma)$ are the term and version of the last accepted state;
- $\mathrm{won}(\sigma)$ is `electionWon`;
- $\mathrm{lpv}(\sigma)$ is `lastPublishedVersion`;
- $\mathrm{pv}(\sigma)$ is the list of ids in the publish votes.

$P.\mathrm{dn}(n) = \langle n, P.\mathrm{eligible}(n)\rangle$ is node $n$'s discovery node.

**Messages.** A publication request $\mathrm{publishRequest}(src, s, pt, pv)$ carries:

- the publisher $src$;
- the published cluster state $s$;
- a ghost parent key $(pt, pv)$, which is the publisher's accepted term and version when it published.

A publish response $\mathrm{publishResponse}(src, dst, \langle \tau, v\rangle)$ goes from $src$ to $dst$ and carries term $\tau$ and version $v$. Messages are never removed.

**The publication period** $\mathrm{PublicationExec}(P, c, t, Q)(W, W')$ is a finite, possibly empty, sequence of `Step`s. Each step is of one of the following kinds:

- **bootstrap** of any node;
- **start-join** at any node $n$, on a request from an eligible requester in term $t'$, where $t' \le t$ is required if $n = c$ or $n \in Q$;
- **join**: unrestricted;
- **client value**, i.e. a new publication, by any node other than $c$;
- **publish**: unrestricted, with no freshness guard;
- **respond**: unrestricted;
- **commit**: unrestricted;
- **restart** of an eligible node other than $c$ (members of $Q$ may restart);
- **restartAny** of a non-eligible node.

**`handlePublishRequest(σ, ⟨s⟩)`**:

- error if $s.\mathrm{term} \ne \mathrm{cur}(\sigma)$;
- otherwise, if $s.\mathrm{term} = \mathrm{lat}(\sigma)$ and $s.\mathrm{version} \le \mathrm{lav}(\sigma)$:
  - error if $s.\mathrm{term} \ne 0$;
  - if $s.\mathrm{term} = 0$ (the Zen1 branch), accept iff $s$ names a cluster-manager node that differs from the one in $\sigma$'s accepted state;
- otherwise accept.

Accepting replaces $\sigma$'s accepted state by $s$ and returns $\langle s.\mathrm{term}, s.\mathrm{version}\rangle$.

**`handlePublishResponse(σ, d, ⟨τ, v⟩)`**:

- error if $\mathrm{won}(\sigma) = \mathrm{false}$;
- error if $\tau \ne \mathrm{cur}(\sigma)$;
- error if $v \ne \mathrm{lpv}(\sigma)$;
- otherwise the new publish-vote list is $\mathrm{addVote}(\mathrm{pv}(\sigma), d).1$, which prepends $d.\mathrm{id}$ if $d$ is flagged cluster-manager and $d.\mathrm{id}$ is not yet present. The handler also returns an apply-commit request when the votes are a quorum of $\sigma$'s last committed and last published configurations.

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
| `t` | $\mathbb{N}$ (its term) |
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
| `W'` | `Cluster V` |
| `hE` | $\mathrm{PublicationExec}(P, c, t, Q)(W, W')$ |

**Conclusion.** The conclusion is the conjunction of (A) and (B).

**(A)**
$$\forall q \in Q,\ \mathrm{cur}(W'.\mathrm{node}\ q) = t \to \Big(\mathrm{publishResponse}(q, c, \langle t, s.\mathrm{version}\rangle) \in W'.\mathrm{sent} \;\lor\; \exists\, cs'\ r,\ \mathrm{handlePublishRequest}(W'.\mathrm{node}\ q, \langle s\rangle) = \mathrm{ok}(cs', r)\Big).$$

Unfolded: let $\sigma_q = W'.\mathrm{node}\ q$, with $\mathrm{cur}(\sigma_q) = t = s.\mathrm{term}$. If $t \ge 1$, the handler succeeds exactly when $\neg(\mathrm{lat}(\sigma_q) = t \land s.\mathrm{version} \le \mathrm{lav}(\sigma_q))$. If $t = 0$, the Zen1 branch could also accept. A reachable cluster with a sent publication of term $t$ has $t \ge 1$, which I derived from the step relation; the statement does not say it. So (A) says: every member of $Q$ that is in term $t$ at $W'$ and has already accepted a term-$t$ state of version $\ge s.\mathrm{version}$ has sent $c$ the acknowledgement $\langle t, s.\mathrm{version}\rangle$. Every other member of $Q$ in term $t$ can accept $s$ now.

**(B)**
$$\forall q \in Q,\ \mathrm{publishResponse}(q, c, \langle t, s.\mathrm{version}\rangle) \in W'.\mathrm{sent} \to \exists\, cs'\ o,\ \mathrm{handlePublishResponse}(W'.\mathrm{node}\ c, P.\mathrm{dn}(q), \langle t, s.\mathrm{version}\rangle) = \mathrm{ok}(cs', o) \land q \in cs'.\mathrm{publishVotes}.\mathrm{nodes}.$$

Unfolded: let $\sigma_c = W'.\mathrm{node}\ c$. The handler's guards say $\mathrm{won}(\sigma_c) = \mathrm{true}$, $\mathrm{cur}(\sigma_c) = t$ and $\mathrm{lpv}(\sigma_c) = s.\mathrm{version}$. The membership $q \in \mathrm{addVote}(\mathrm{pv}(\sigma_c), P.\mathrm{dn}(q)).1$ then holds automatically, because $P.\mathrm{dn}(q)$ is flagged cluster-manager by `hQ`. So (B) amounts to: if at least one member of $Q$ has acknowledged $s$ to $c$ by $W'$, then at $W'$ the node $c$ is still elected, still in term $t$, and its last published version is still $s.\mathrm{version}$.

## 2. What is not constrained

- **$c$'s eligibility.** It is not assumed. In a reachable cluster only eligible nodes ever have $\mathrm{won} = \mathrm{true}$, so `hwon` implies it. I derived this from the step relation: joins are addressed only to eligible requesters.
- **No quorum or term hypothesis on $Q$.**
  - Members of $Q$ that are not in term $t$ at $W'$ are not covered by (A).
  - Members above $t$ at $W$ stay above $t$, since start-joins only raise terms and eligible nodes keep their term on restart. They are never covered.
  - Members below $t$ need a start-join into $t$ first. The period allows it ($t' \le t$), and `handleStartJoin`'s only guard is the term comparison, but the theorem does not state that this step is enabled.
- **The ghost parent.** $pt$ and $pv$ are unconstrained apart from `hs`.
- **Scope of (A).**
  - In (A), the acknowledgement may have been sent before $W$.
  - (A)'s second disjunct is about the pure handler applied to $q$'s state. The corresponding publish step, for the message $(c, s, pt, pv)$, is available at $W'$ because `sent` only grows and the publication period puts no guard on `publish`.
- **Scope of (B).**
  - (B) is triggered only by an existing acknowledgement from a member of $Q$. If no member of $Q$ has acknowledged, it says nothing about $c$.
  - Acknowledgements from non-members, or with other versions, are not addressed.
  - (B) implicitly asserts that $c$ cannot lose `electionWon` while it handles further joins during the period. Java asserts this (`CoordinationState.java:323`). Nothing in the Lean handlers enforces it, so it must follow from reachability under the default strategy (`hes`).
- **No quorum or commit claim.** Neither conjunct says that a quorum of acknowledgements is reached, or anything about commits.
- **Model-relative.** In the model, every successful `handlePublishRequest` sends an acknowledgement, and that acknowledgement stays deliverable. In Java, a failing remote-store write makes the method throw after the local acceptance (`CoordinationState.java:453-456`), so no acknowledgement is sent. The Coordination file abstracts this away; see G5 in the definitions read-back. In that case neither disjunct of (A) would hold for that voter in OpenSearch: no acknowledgement exists, and re-handling $s$ is rejected because the version is not newer.
- **Role of `hsv`.** `hsv` pins $s$ as $c$'s latest publication at $W$. Its version is the one that $c$'s handler accepts in acknowledgements.
- **What the period still allows.** During the period:
  - nodes outside $\{c\} \cup Q$ may move to any term, win, and publish;
  - members of $Q$ may restart, bootstrap (if the contract allows), and accept any publication of their current term;
  - only $c$ is barred from publishing further.
- **Empty execution and vacuity.**
  - The empty execution ($W' = W$) is allowed, and then the theorem is a statement about $W$ itself.
  - If $Q = [\,]$, both conjuncts are vacuous.
  - The hypotheses are satisfiable. Single-node example: node 1 is eligible, the bootstrap configuration is $\{1\}$ only, and the strategy is the default. Node 1 bootstraps, start-joins on its own request for term 1, handles its own join (and wins), and publishes $s$ of term 1 and version 1. Then $W$ is the cluster right after the publication, with $c = 1$, $t = 1$ and $Q = [1]$.

## 3. Plain-language summary

Suppose that, in a reachable cluster, $c$ has won term $t$ and has sent $s$ as its latest publication. Then, throughout any stable publication period, the following hold:

- In this period no node of $\{c\} \cup Q$ moves above $t$, $c$ neither publishes again nor restarts, and everything else may happen.
- Every eligible member of $Q$ that is in term $t$ has either already acknowledged $s$ to $c$, or can still accept $s$.
- As soon as a member of $Q$ has acknowledged $s$ to $c$, $c$ can still count that acknowledgement.

The theorem covers only members of $Q$ already in term $t$. It does not claim that acknowledgements are sent, that a quorum is reached, or that anything is committed.
