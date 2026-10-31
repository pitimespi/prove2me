# Read-back: `Def_OpenSearchProgress.lean`

The file declares four inductive relations in the namespace `OpenSearchProgress` and nothing else: `ElectionStep`, `ElectionExec`, `PublicationStep`, `PublicationExec`. Each relates two clusters (`Cluster V → Cluster V → Prop`) and is indexed by fixed parameters. The payload type `V` is an implicit parameter throughout. The file imports `Def_OpenSearchSafety`, which imports `Def_OpenSearchCoordination`. The imported notions are expanded first, so that each declaration can be read on its own. The module docstring describes "stable periods" for an election and for a publication; the last section compares it with the terms.

## Imported notions, expanded

### Notation used in this read-back

For a node state $\sigma$ (a `CoordinationState V`), write:

- $\mathrm{ln}(\sigma)$ for `localNode`, $\mathrm{cur}(\sigma)$ for `currentTerm` (a natural number) and $\mathrm{acc}(\sigma)$ for `lastAcceptedState` (a cluster state);
- $\mathrm{lat}(\sigma) = \mathrm{acc}(\sigma).\mathrm{term}$ and $\mathrm{lav}(\sigma) = \mathrm{acc}(\sigma).\mathrm{version}$ (an integer). $\mathrm{lavm}(\sigma)$ is `lastAcceptedVersionOrMetadataVersion`: it equals $\mathrm{acc}(\sigma).\mathrm{metadataVersion}$ if $\mathrm{acc}(\sigma).\mathrm{term} = 0$, and $\mathrm{acc}(\sigma).\mathrm{version}$ otherwise;
- $\mathrm{lcc}(\sigma)$ and $\mathrm{lac}(\sigma)$ for the last committed and last accepted configuration of $\mathrm{acc}(\sigma)$;
- $\mathrm{jv}(\sigma)$ and $\mathrm{pv}(\sigma)$ for the lists of node ids of `joinVotes` and `publishVotes`;
- $\mathrm{sj}(\sigma)$ for `startedJoinSinceLastReboot` and $\mathrm{won}(\sigma)$ for `electionWon` (both Booleans), $\mathrm{lpv}(\sigma)$ for `lastPublishedVersion` (an integer) and $\mathrm{lpc}(\sigma)$ for `lastPublishedConfiguration`.

"$\sigma$ with $f := x$" means $\sigma$ with field $f$ replaced and every other field unchanged. For *keys*, meaning pairs of a natural-number term and an integer version, $(a, b) \preceq (a', b')$ means $a < a' \lor (a = a' \land b \le b')$. This is the lexicographic order; the Safety file names it `KeyLE`, but the Progress file writes it out inline.

### Node ids, discovery nodes, parameters, strategies

- A **node id** is a natural number. Only equality is used. A **discovery node** $d$ is a pair of an id $d.\mathrm{id}$ and a Boolean $d.\mathrm{isClusterManagerNode}$.
- The **parameters** $P$ consist of:
  - a Boolean function $P.\mathrm{eligible}$ on node ids (cluster-manager eligibility);
  - an arbitrary predicate $P.\mathrm{initConfs}$ on voting configurations (the configurations a node may bootstrap with);
  - an election strategy $P.\mathrm{strategy}$.

  We write $P.\mathrm{dn}(n) = \langle n, P.\mathrm{eligible}(n)\rangle$.
- An **election strategy** is a single Boolean function `satisfiesAdditionalQuorumConstraints` of seven arguments: the local node, current term, accepted term, accepted version, last committed configuration, last accepted configuration and vote collection. `ElectionStrategy.DEFAULT_INSTANCE` returns `true` for all arguments.
- $P.\mathrm{InitCompatible}$ is used as a hypothesis by every theorem. It says: for all configurations $X, Y$ with $P.\mathrm{initConfs}(X)$ and $P.\mathrm{initConfs}(Y)$, and all lists $q_1, q_2$ of ids whose members are all eligible, if $\mathrm{Quorum}(X, q_1)$ and $\mathrm{Quorum}(Y, q_2)$ then some $x$ belongs to both $q_1$ and $q_2$. It holds vacuously if $P.\mathrm{initConfs}$ admits nothing. It also holds, for example, if $P.\mathrm{initConfs}$ admits exactly one configuration, because any two majorities of one set intersect.

### Voting configurations, quorums, vote collections

- A **voting configuration** $X$ is a strictly increasing list of ids $X.\mathrm{ids}$. It is therefore duplicate-free, and equality of configurations is equality of the id lists, i.e. of the id sets. $\mathrm{EMPTY}$ has no ids. "$X$ is empty" (`isEmpty`) means $X.\mathrm{ids} = [\,]$.
- For a list $L$ of ids, $\mathrm{Quorum}(X, L)$ (Lean `X.hasQuorum L = true`) means
  $$2 \cdot \big|\{x \in X.\mathrm{ids} : x \in L\}\big| > |X.\mathrm{ids}|.$$
  Properties:
  - it is false whenever $X$ is empty, and false whenever $L = [\,]$;
  - it is monotone in $L$: if every member of $L$ is in $L'$, then $\mathrm{Quorum}(X, L) \to \mathrm{Quorum}(X, L')$;
  - duplicates in $L$, and members of $L$ outside $X$, are irrelevant.
- A **vote collection** is a list of ids. $\mathrm{addVote}(v, d)$ returns $(d.\mathrm{id} :: v,\ \mathrm{true})$ if $d.\mathrm{isClusterManagerNode} = \mathrm{true}$ and $d.\mathrm{id} \notin v$, and $(v, \mathrm{false})$ otherwise. So after $\mathrm{addVote}(v, d)$, the id $d.\mathrm{id}$ is in the collection exactly when it already was, or $d$ is flagged cluster-manager. $\mathrm{isQuorum}(v, X) = \mathrm{Quorum}(X, v)$.

### Cluster states and messages

- A **cluster state** $s$ has the following fields:
  - $s.\mathrm{term} \in \mathbb{N}$, $s.\mathrm{version} \in \mathbb{Z}$ and $s.\mathrm{metadataVersion} \in \mathbb{Z}$;
  - two configurations, $s.\mathrm{lcc}$ (last committed) and $s.\mathrm{lac}$ (last accepted);
  - an optional natural number $s.\mathrm{clusterManagerNode}$;
  - two Booleans, `clusterUUIDKnown` and `clusterUUIDCommitted`;
  - a payload in $V$.
- $\mathrm{markCommitted}(s)$ works in two steps:
  1. if $s.\mathrm{lac} \ne s.\mathrm{lcc}$, it sets $s.\mathrm{lcc} := s.\mathrm{lac}$;
  2. then, if `clusterUUIDKnown` holds and `clusterUUIDCommitted` does not, it sets `clusterUUIDCommitted := true`.

  Term, version, metadata version, $\mathrm{lac}$ and payload are unchanged.
- The message payloads are:
  - A **join** $j$ has a source and a target discovery node ($j.\mathrm{sourceNode}$, $j.\mathrm{targetNode}$), a term $j.\mathrm{term} \in \mathbb{N}$, and the voter's last accepted term $j.\mathrm{lastAcceptedTerm} \in \mathbb{N}$ and version $j.\mathrm{lastAcceptedVersion} \in \mathbb{Z}$. The version is filled by `handleStartJoin` with $\mathrm{lavm}$, so for a term-0 accepted state it is the metadata version.
  - A **publish request** is $\langle s\rangle$, a single cluster state.
  - A **publish response** is $\langle \tau, v\rangle$, a term and a version.
  - An **apply-commit request** is $\langle d, \tau, v\rangle$: a source discovery node, a term and a version.
- A **message** is one of four kinds:
  - $\mathrm{join}(j)$;
  - $\mathrm{publishRequest}(src, s, pt, pv)$: a request from node $src$ carrying state $s$ and a "ghost" parent key $(pt, pv)$;
  - $\mathrm{publishResponse}(src, dst, r)$: a response from $src$ to $dst$;
  - $\mathrm{applyCommit}(a)$.

  Publish requests and commits carry no addressee. A join's addressee is $j.\mathrm{targetNode}$.

### Node states and handlers

A **node state** has the fields listed in the notation. $\mathrm{init}(d, \tau, a)$ is the node state with localNode $d$, current term $\tau$, accepted state $a$, join votes $[\,]$, $\mathrm{sj} = \mathrm{false}$, $\mathrm{won} = \mathrm{false}$, $\mathrm{lpv} = 0$, $\mathrm{lpc} = a.\mathrm{lac}$ and publish votes $[\,]$.

Each handler returns either an error or $\mathrm{ok}(\text{result})$. Its guards are tested in the order listed, and the first guard that holds yields an error.

- **setInitialState$(\sigma, s)$** is an error if $\mathrm{lac}(\sigma)$ is non-empty. Otherwise it is $\mathrm{ok}(\sigma \text{ with } \mathrm{acc} := s)$.
  - **initialStateContract$(\sigma, s)$** is a separate proposition that the handler does not check. It requires $\mathrm{lat}(\sigma) = 0$; $\mathrm{lcc}(\sigma)$ empty; $\mathrm{lpv}(\sigma) = 0$; $\mathrm{lpc}(\sigma)$ empty; $\mathrm{won}(\sigma) = \mathrm{false}$; $\mathrm{jv}(\sigma) = [\,]$; $\mathrm{pv}(\sigma) = [\,]$; $s.\mathrm{term} = 0$; $s.\mathrm{version} = \mathrm{lav}(\sigma)$; and $s.\mathrm{lac}$ and $s.\mathrm{lcc}$ non-empty.
- **handleStartJoin$(\sigma, \langle d, \tau\rangle)$** is an error if $\tau \le \mathrm{cur}(\sigma)$. Otherwise it is $\mathrm{ok}(\sigma', j)$, where:
  - $\sigma'$ is $\sigma$ with $\mathrm{cur} := \tau$, $\mathrm{lpv} := 0$, $\mathrm{lpc} := \mathrm{lac}(\sigma)$, $\mathrm{sj} := \mathrm{true}$, $\mathrm{won} := \mathrm{false}$, $\mathrm{jv} := [\,]$ and $\mathrm{pv} := [\,]$;
  - $j = \langle \mathrm{ln}(\sigma), d, \tau, \mathrm{lat}(\sigma), \mathrm{lavm}(\sigma)\rangle$, whose source is this node's localNode and whose target is the requester $d$.
- **handleJoin$(es, \sigma, j)$**:
  1. error if $j.\mathrm{term} \ne \mathrm{cur}(\sigma)$;
  2. error if $\mathrm{sj}(\sigma) = \mathrm{false}$;
  3. error if $j.\mathrm{lastAcceptedTerm} > \mathrm{lat}(\sigma)$;
  4. error if $j.\mathrm{lastAcceptedTerm} = \mathrm{lat}(\sigma)$ and $j.\mathrm{lastAcceptedVersion} > \mathrm{lavm}(\sigma)$;
  5. error if $\mathrm{lac}(\sigma)$ is empty;
  6. otherwise:
     - let $(v, \mathit{added}) = \mathrm{addVote}(\mathrm{jv}(\sigma), j.\mathrm{sourceNode})$ and $w = \mathrm{isElectionQuorum}(es, \sigma, v)$;
     - let $\sigma_1$ be $\sigma$ with $\mathrm{jv} := v$ and $\mathrm{won} := w$;
     - let $\sigma_2$ be $\sigma_1$ with $\mathrm{lpv} := \mathrm{lav}(\sigma)$ if $w \land \neg \mathrm{won}(\sigma)$, and $\sigma_1$ otherwise;
     - the result is $\mathrm{ok}(\sigma_2, \mathit{added})$.

  Here $\mathrm{isElectionQuorum}(es, \sigma, v) = \mathrm{Quorum}(\mathrm{lcc}(\sigma), v) \land \mathrm{Quorum}(\mathrm{lac}(\sigma), v) \land es.\mathrm{satisfies}(\mathrm{ln}(\sigma), \mathrm{cur}(\sigma), \mathrm{lat}(\sigma), \mathrm{lav}(\sigma), \mathrm{lcc}(\sigma), \mathrm{lac}(\sigma), v)$. For the default strategy this is just the two quorums. The configurations are $\sigma$'s, which the handler does not change. The target node of $j$ is not examined. Whether the handler succeeds, and the new vote list, do not depend on the strategy: only $\mathrm{won}$ and $\mathrm{lpv}$ do. `won` is recomputed on every successful join, and the handler itself does not prevent it from going from true to false. Java asserts that this never happens; see the citation check. Whether it can happen in a reachable cluster is not addressed by any definition.
- **handleClientValue$(\sigma, s)$** returns an error, in this order:
  - if $\mathrm{won}(\sigma) = \mathrm{false}$;
  - if $\mathrm{lpv}(\sigma) \ne \mathrm{lav}(\sigma)$;
  - if $s.\mathrm{term} \ne \mathrm{cur}(\sigma)$;
  - if $s.\mathrm{version} \le \mathrm{lpv}(\sigma)$;
  - if $s.\mathrm{lac} \ne \mathrm{lac}(\sigma)$ and $\mathrm{lcc}(\sigma) \ne \mathrm{lac}(\sigma)$;
  - if $\neg\mathrm{Quorum}(s.\mathrm{lac}, \mathrm{jv}(\sigma))$.

  Otherwise it returns $\mathrm{ok}(\sigma \text{ with } \mathrm{lpv} := s.\mathrm{version}, \mathrm{lpc} := s.\mathrm{lac}, \mathrm{pv} := [\,];\ \langle s\rangle)$. Its contract **clientValueContract$(\sigma, s)$** is $s.\mathrm{lcc} = \mathrm{lcc}(\sigma)$.
- **handlePublishRequest$(\sigma, \langle s\rangle)$**:
  - error if $s.\mathrm{term} \ne \mathrm{cur}(\sigma)$;
  - else, if $s.\mathrm{term} = \mathrm{lat}(\sigma)$ and $s.\mathrm{version} \le \mathrm{lav}(\sigma)$:
    - if $s.\mathrm{term} = 0$ (the "Zen1" branch): error if $s.\mathrm{clusterManagerNode}$ is none; accept if it is some $m$ with $\mathrm{some}\ m \ne \mathrm{acc}(\sigma).\mathrm{clusterManagerNode}$; error otherwise;
    - if $s.\mathrm{term} \ne 0$: error;
  - otherwise, accept.

  "Accept" means $\mathrm{ok}(\sigma \text{ with } \mathrm{acc} := s,\ \text{response } \langle s.\mathrm{term}, s.\mathrm{version}\rangle)$.
- **handlePublishResponse$(\sigma, d, \langle \tau, v\rangle)$** returns an error if $\mathrm{won}(\sigma) = \mathrm{false}$, if $\tau \ne \mathrm{cur}(\sigma)$, or if $v \ne \mathrm{lpv}(\sigma)$. Otherwise, let $v' = \mathrm{addVote}(\mathrm{pv}(\sigma), d).1$ and let $\sigma'$ be $\sigma$ with $\mathrm{pv} := v'$.
  - If $\mathrm{Quorum}(\mathrm{lcc}(\sigma), v') \land \mathrm{Quorum}(\mathrm{lpc}(\sigma), v')$ (this conjunction is `isPublishQuorum`), the result is $\mathrm{ok}(\sigma', \mathrm{some}\ \langle \mathrm{ln}(\sigma), \tau, v\rangle)$.
  - Otherwise it is $\mathrm{ok}(\sigma', \mathrm{none})$.
- **handleCommit$(\sigma, \langle d, \tau, v\rangle)$** returns an error if $\tau \ne \mathrm{cur}(\sigma)$, if $\tau \ne \mathrm{lat}(\sigma)$, or if $v \ne \mathrm{lav}(\sigma)$. Otherwise it returns $\mathrm{ok}(\sigma \text{ with } \mathrm{acc} := \mathrm{markCommitted}(\mathrm{acc}(\sigma)))$. The source $d$ is not examined.

### Clusters, steps, reachability

- A **cluster** $W$ has $W.\mathrm{node}$, a node state for every id, and $W.\mathrm{sent}$, a set of messages given as a predicate.
  - $W.\mathrm{set}(n, \sigma)$ replaces node $n$'s state by $\sigma$ and leaves the other nodes and `sent` unchanged.
  - $W.\mathrm{send}(m)$ adds $m$ to `sent` and leaves the nodes unchanged.

  No operation removes a message.
- **RestartState$(a, a')$** relates a node's old accepted state $a$ to its new one $a'$. It holds in one of two cases:
  - First case: $a'$ has the same term, version, $\mathrm{lcc}$, $\mathrm{lac}$, `clusterUUIDKnown` and `clusterUUIDCommitted` as $a$. Metadata version, cluster-manager node and payload are free.
  - Second case: $a$ has term 0, both configurations empty and `clusterUUIDKnown = false`, and $a'$ has term 0 and both configurations empty. Everything else about $a'$ is free.
- **Step$(P)(W, W')$** holds in exactly the following nine cases, where $\sigma = W.\mathrm{node}(n)$ for the acting node $n$:
  1. *bootstrap* $(n, X, s, cs')$:
     - guards: $P.\mathrm{initConfs}(X)$; $\mathrm{initialStateContract}(\sigma, s)$; $s.\mathrm{lcc} = X \land s.\mathrm{lac} = X$; $\mathrm{setInitialState}(\sigma, s) = \mathrm{ok}\ cs'$;
     - result: $W' = W.\mathrm{set}(n, cs')$.
  2. *startJoin* $(n, src, \tau, cs', j)$:
     - guards: $P.\mathrm{eligible}(src)$; $\mathrm{handleStartJoin}(\sigma, \langle P.\mathrm{dn}(src), \tau\rangle) = \mathrm{ok}(cs', j)$;
     - result: $W' = W.\mathrm{set}(n, cs').\mathrm{send}(\mathrm{join}\ j)$.

     No start-join *message* is required. Any node may act on a request "from" any eligible node in any term.
  3. *join* $(n, j, cs', b)$:
     - guards: $\mathrm{join}\ j \in W.\mathrm{sent}$; $j.\mathrm{targetNode}.\mathrm{id} = n$; $\mathrm{handleJoin}(P.\mathrm{strategy}, \sigma, j) = \mathrm{ok}(cs', b)$;
     - result: $W' = W.\mathrm{set}(n, cs')$.
  4. *clientValue* $(n, s, cs', p)$:
     - guards: $\mathrm{clientValueContract}(\sigma, s)$; $\mathrm{handleClientValue}(\sigma, s) = \mathrm{ok}(cs', p)$;
     - result: $W' = W.\mathrm{set}(n, cs').\mathrm{send}(\mathrm{publishRequest}(n, s, \mathrm{lat}(\sigma), \mathrm{lav}(\sigma)))$. The state in $p$ is $s$.
  5. *publish* $(n, src, s, pt, pv, cs', r)$:
     - guards: $\mathrm{publishRequest}(src, s, pt, pv) \in W.\mathrm{sent}$; $\mathrm{handlePublishRequest}(\sigma, \langle s\rangle) = \mathrm{ok}(cs', r)$;
     - result: $W' = W.\mathrm{set}(n, cs').\mathrm{send}(\mathrm{publishResponse}(n, src, r))$.
  6. *respond* $(n, src, r, cs', o)$:
     - guards: $\mathrm{publishResponse}(src, n, r) \in W.\mathrm{sent}$; $\mathrm{handlePublishResponse}(\sigma, P.\mathrm{dn}(src), r) = \mathrm{ok}(cs', o)$;
     - result: $W' = W.\mathrm{set}(n, cs')$ if $o = \mathrm{none}$, and $W.\mathrm{set}(n, cs').\mathrm{send}(\mathrm{applyCommit}\ a)$ if $o = \mathrm{some}\ a$.
  7. *commit* $(n, a, cs')$:
     - guards: $\mathrm{applyCommit}\ a \in W.\mathrm{sent}$; $\mathrm{handleCommit}(\sigma, a) = \mathrm{ok}\ cs'$;
     - result: $W' = W.\mathrm{set}(n, cs')$.
  8. *restart* $(n, s')$:
     - guards: $P.\mathrm{eligible}(n)$; $\mathrm{RestartState}(\mathrm{acc}(\sigma), s')$;
     - result: $W' = W.\mathrm{set}(n, \mathrm{init}(\mathrm{ln}(\sigma), \mathrm{cur}(\sigma), s'))$. The current term is kept.
  9. *restartAny* $(n, \tau, s')$:
     - guard: $P.\mathrm{eligible}(n) = \mathrm{false}$;
     - result: $W' = W.\mathrm{set}(n, \mathrm{init}(\mathrm{ln}(\sigma), \tau, s'))$, with an arbitrary term $\tau$ and an arbitrary state $s'$.
- **Initial$(P)(W)$**: no message is sent, and every node $n$ has $W.\mathrm{node}(n) = \mathrm{init}(P.\mathrm{dn}(n), 0, s)$ for some state $s$ with term 0 and both configurations empty. Version, metadata version, payload, cluster-manager node and UUID flags are free and may differ per node.
- **Reachable$(P)$** is the least set of clusters that contains every initial cluster and is closed under $\mathrm{Step}(P)$.
- **Committed$(W, \tau, v)$**: some apply-commit request $\langle d, \tau, v\rangle$, with any source $d$, is in $W.\mathrm{sent}$.

The Safety file also defines `BootstrapConfig`, `Parent`, `Descends`, `KeyLE`, `Below`, `Published`, `Realizes`, `JoinVoters`, `BaseVoters`, `RespVoters`, `ElectionRecord`, `Won` and the invariant `Inv`. None of them occurs in `Def_OpenSearchProgress.lean` or in the six theorem statements of this mission.

## Java citation check

The Progress file cites no Java. Its four relations reuse the handlers of `Def_OpenSearchCoordination` (cited as `CS:` = `CoordinationState.java` and so on, at OpenSearch revision `b2a54ba5…`). The local checkout `/home/user/opensearch-project/OpenSearch` is at exactly that revision. I compared every handler and helper that the progress definitions and theorems rely on.

| Lean | Cited Java | Verdict |
|---|---|---|
| `CoordinationState.init` | CS:84-106 | Matches. The remote-state flag is omitted. |
| `isElectionQuorum` | CS:144-154; ES:68-88 | Matches: committed quorum ∧ accepted quorum ∧ additional constraint. |
| `isPublishQuorum` | CS:156-158 | Matches. |
| `setInitialState`, `initialStateContract` | CS:180-204 (asserts CS:190-201) | Matches. The 11 assertions are the 11 conjuncts of the contract. |
| `handleStartJoin` | CS:213-255 | Matches. The logging branch is omitted. |
| `handleJoin` | CS:264-339 | Matches. Java's `addJoinVote(join)` is `addVote(join.getSourceNode())` plus recording the join, CS:759-765. Two assertions are not checked: CS:265 (target matches local node) and CS:323, "we cannot go from won to not won". |
| `handleClientValue`, `clientValueContract` | CS:348-407 (assert CS:397-398) | Matches. |
| `handlePublishRequest` | CS:416-460 | Matches, including the Zen1 branch: a null incoming cluster-manager throws in Java and is an error here. The remote write is omitted. |
| `handlePublishResponse` | CS:471-515 | Matches. `handlePreCommit()` (remote state, CS:510) is omitted. |
| `handleCommit`, `markCommitted` | CS:523-573; CS:703-740 | Matches. The remote commit and the assertions CS:572 and CS:708-710 are omitted. |
| `VoteCollection.addVote`, `isQuorum` | CS:755-757; CS:772-774 | Matches. The Java map of discovery nodes keyed by id becomes a list of ids. |
| `VotingConfiguration.hasQuorum` | CM:405-409 | Matches. The ids are sorted and duplicate-free, so the filter length equals the size of the intersection. |
| `ElectionStrategy.DEFAULT_INSTANCE` | ES:46-59 | Matches: always `true`. |
| `versionOrMetadataVersion` | CLS:239-244 | Matches. |
| `ZEN1_BWC_TERM` | Coordinator.java:134 | Matches: 0. |

I also spot-checked the restart description in the Safety file (`GatewayMetaState.java:141-256`), and it is consistent at the level I checked:

- the on-disk term, version and metadata are loaded;
- remote restore happens only when the local cluster UUID is unknown;
- the role-change caveat at 232-255 is the branch for nodes that are neither cluster-manager nor data nodes, which persists term 0.

I did not check the Safety file's `Coordinator.java` (CO:1101-1161) or `ClusterBootstrapService` citations. No transcription mismatch was found.

One item in the table bears on this mission. Java asserts at CS:323 that `electionWon` never goes from true to false in `handleJoin`. In Java production builds assertions are disabled, and in the Lean model nothing enforces this. In a publication period the cluster-manager $c$ may still handle joins. Some publication theorems implicitly require that $c$ stays elected: conjunct (B) of `publication_acks_accepted`, and `publication_committed`. They therefore rely on this being a consequence of reachability, under the default strategy they assume.

## Declaration 1: `ElectionStep P c t Q kt kv`

**Parameters.**

- $P$: parameters.
- $c$: a node id, the "candidate".
- $t \in \mathbb{N}$: the "term".
- $Q$: a list of node ids, the "voters".
- $k_t \in \mathbb{N}$ and $k_v \in \mathbb{Z}$.

The definition does not relate these to each other:

- $c$ need not be eligible, and $c$ may belong to $Q$;
- $Q$ may be empty or contain duplicates;
- $(k_t, k_v)$ is an arbitrary key. The docstring reads it as "the term and version of $c$'s accepted state when the period starts", but only the theorems' instantiation supplies that meaning.

**Cases.** $\mathrm{ElectionStep}_{P,c,t,Q,k_t,k_v}(W, W')$ holds in exactly the following eight cases, where $\sigma = W.\mathrm{node}(n)$:

1. **bootstrap** $(n, X, s, cs')$: all hypotheses of Step case 1, plus $n \ne c \land n \notin Q$. Result: $W.\mathrm{set}(n, cs')$.
2. **startJoin** $(n, src, t', cs', j)$: all hypotheses of Step case 2 with request term $t'$, plus
   $$t' < t \;\lor\; (src = c \land t' = t).$$
   Result: $W.\mathrm{set}(n, cs').\mathrm{send}(\mathrm{join}\ j)$. The guard applies to *every* acting node $n$, not only to $c$ and $Q$.
3. **join** $(n, j, cs', b)$: exactly Step case 3, with no extra guard.
4. **publish** $(n, src, s, pt, pv, cs', r)$: all hypotheses of Step case 5, plus
   $$(n = c \lor n \in Q) \;\to\; \big(s.\mathrm{term} < k_t \lor (s.\mathrm{term} = k_t \land s.\mathrm{version} \le k_v)\big),$$
   that is, if the receiver is $c$ or a voter, then $(s.\mathrm{term}, s.\mathrm{version}) \preceq (k_t, k_v)$. Result: $W.\mathrm{set}(n, cs').\mathrm{send}(\mathrm{publishResponse}(n, src, r))$. Other receivers are unrestricted.
5. **respond** $(n, src, r, cs', o)$: exactly Step case 6.
6. **commit** $(n, a, cs')$: exactly Step case 7.
7. **restart** $(n, s')$: all hypotheses of Step case 8, plus $n \ne c \land n \notin Q$. Result: $W.\mathrm{set}(n, \mathrm{init}(\mathrm{ln}(\sigma), \mathrm{cur}(\sigma), s'))$.
8. **restartAny** $(n, t'', s')$: exactly Step case 9. There is no condition relating $n$ to $c$ or $Q$; the only guard is $P.\mathrm{eligible}(n) = \mathrm{false}$.

There is **no case for Step's `clientValue`**: no node sends a new publication request during an election period.

**What the guards amount to.** I derived these from the handlers; the file does not state them.

- *Start-joins.* `handleStartJoin` requires $t' > \mathrm{cur}(\sigma)$ and the guard requires $t' \le t$. So a node whose current term is $\ge t$ cannot start-join at all during the period. A node in a term $< t$ can move, through start-joins:
  - to any term strictly between its term and $t$, on a request from any eligible requester;
  - to $t$ itself only on a request whose requester is $c$.

  No node's term passes $t$ through a start-join. A non-eligible node can still receive any term through `restartAny`.
- *Publications.* Only publication requests already in $W.\mathrm{sent}$ at the start of the period can be handled. Responses and commits can still be produced from them.
- *Freshness bound at $c$.* Take the theorems' instantiation, $(k_t, k_v) = (\mathrm{lat}, \mathrm{lav})$ of $c$ at the start, in a reachable cluster with $c$ eligible. Then $c$ can accept no publication during the period. The reasons:
  - Acceptance requires $s.\mathrm{term} = \mathrm{cur}(c) \ge \mathrm{lat}(c) = k_t$, so the guard forces $s.\mathrm{term} = k_t$ and $s.\mathrm{version} \le k_v$.
  - The handler rejects that case unless $s.\mathrm{term} = 0$.
  - Sent publications have term $\ge 1$ (observation G3 below).

  So $c$'s accepted term, version and $\mathrm{lac}$ stay fixed during the period, and only a commit can change $\mathrm{lcc}(c)$, to $\mathrm{lac}(c)$. The voters' accepted keys can grow, but only to keys $\preceq (k_t, k_v)$.
- *Version measure.* The bound $k_v$ is compared with $s.\mathrm{version}$. `handleJoin` instead compares joins against $\mathrm{lavm}$, the metadata version at term 0. When $k_t = 0$, the guard admits only term-0 publications, and none exist in a reachable cluster (observation G3). So $c$ and the voters accept nothing in that case, and the two version measures never interact.

## Declaration 2: `ElectionExec P c t Q kt kv`

$\mathrm{ElectionExec}(W, W')$ is the reflexive-transitive closure of `ElectionStep`, built by appending steps at the end:

- $\mathrm{ElectionExec}(W, W)$ holds for every $W$;
- if $\mathrm{ElectionExec}(W, W')$ and $\mathrm{ElectionStep}(W', W'')$, then $\mathrm{ElectionExec}(W, W'')$.

Equivalently, there are $m \ge 0$ and clusters $W = W_0, \dots, W_m = W'$ such that each consecutive pair is an election step for the same parameters $P, c, t, Q, k_t, k_v$. The empty execution ($m = 0$, $W' = W$) is included.

## Declaration 3: `PublicationStep P c t Q`

**Parameters.**

- $P$: parameters.
- $c$: a node id, "the cluster-manager of term $t$".
- $t \in \mathbb{N}$.
- $Q$: a list of node ids, "acknowledging nodes".

None of them is constrained by the definition. In particular, $c$ is not required to have won or to be in term $t$.

**Cases.** $\mathrm{PublicationStep}_{P,c,t,Q}(W, W')$ holds in exactly the following nine cases, where $\sigma = W.\mathrm{node}(n)$:

1. **bootstrap**: exactly Step case 1. There is no condition on $n$, so $c$ and members of $Q$ may bootstrap if the contract holds.
2. **startJoin** $(n, src, t', cs', j)$: all hypotheses of Step case 2, plus $(n = c \lor n \in Q) \to t' \le t$. Nodes outside $\{c\} \cup Q$ may start-join to any term.
3. **join**: exactly Step case 3.
4. **clientValue** $(n, s, cs', p)$: all hypotheses of Step case 4, plus $n \ne c$. Result: $W.\mathrm{set}(n, cs').\mathrm{send}(\mathrm{publishRequest}(n, s, \mathrm{lat}(\sigma), \mathrm{lav}(\sigma)))$. Every node other than $c$ may still publish.
5. **publish**: exactly Step case 5. There is no freshness restriction.
6. **respond**: exactly Step case 6.
7. **commit**: exactly Step case 7.
8. **restart** $(n, s')$: all hypotheses of Step case 8, plus $n \ne c$. Members of $Q$ may restart.
9. **restartAny**: exactly Step case 9, with no condition relating $n$ to $c$.

**What the guards amount to.** These are derived, not stated.

- Suppose $\mathrm{cur}(c) = t$ at the start, as in all publication theorems. Then $c$'s term stays $t$ throughout: a start-join at $c$ would need $t' > t$ and $t' \le t$; `restart` is excluded for $c$; and `restartAny` needs $c$ non-eligible. In a reachable cluster only eligible nodes ever have $\mathrm{won} = \mathrm{true}$ (observation G3), so a $c$ with $\mathrm{won}(c) = \mathrm{true}$ is eligible.
- $c$ cannot publish again, but it can still handle joins, publications, responses and commits.
- A member of $Q$ in a term $< t$ can move to any term $\le t$, on a request from any eligible requester. A member of $Q$ in a term $\ge t$ cannot start-join.

## Declaration 4: `PublicationExec P c t Q`

`PublicationExec` is the reflexive-transitive closure of `PublicationStep`, with the same shape as `ElectionExec`: zero or more publication steps for fixed $P, c, t, Q$.

## Relation to `Step`, and general observations

These observations are derived by the auditor; the file states none of them.

- **G1.** Each constructor of `ElectionStep` and `PublicationStep` carries exactly the hypotheses of the same-named `Step` constructor plus the extra guards listed above, and produces the same resulting cluster. Hence every election or publication step is a `Step`, and an `ElectionExec` or `PublicationExec` starting from a reachable cluster ends in a reachable cluster.
- **G2.** Along every step, and hence every execution, $W.\mathrm{sent} \subseteq W'.\mathrm{sent}$. A message present at the start of a period remains available, and can be handled any number of times.
- **G3.** In a reachable cluster the following hold, read off the step relation directly and not through `Inv`:
  - every node's localNode is $P.\mathrm{dn}(n)$. `Initial` sets it, `set` and `init` keep it, and no handler changes it;
  - every sent join $j$ has $j.\mathrm{sourceNode} = P.\mathrm{dn}(m)$ for the node $m$ that produced it, and $j.\mathrm{targetNode} = P.\mathrm{dn}(src)$ for an eligible $src$. So only eligible nodes ever handle a join;
  - $\mathrm{won}$ becomes true only in `handleJoin`, so only eligible nodes ever have $\mathrm{won} = \mathrm{true}$;
  - for eligible nodes, $\mathrm{lat} \le \mathrm{cur}$, and $\mathrm{cur}$ never decreases;
  - every sent publication has term $\ge 1$. Its term is the publisher's current term while the publisher is elected. Being elected requires $\mathrm{sj} = \mathrm{true}$, which requires a start-join since the last restart, which makes the term $\ge 1$.
- **G4.** Executions are finite, and no fairness or eventual delivery is part of either relation. Every message stays available, but no step is ever forced to occur.
- **G5.** The Coordination file states its own abstraction for a failed remote write. Java throws after the local effects; the transcription returns the result instead. For safety this only adds behaviours: a result that is sent but never delivered is equivalent to the Java throw. For the progress statements it has a consequence. In the model, an acceptance always yields a publish response that stays deliverable, and a counted quorum always yields a commit. Java can accept a publication locally and then throw, sending no response; a re-delivery of the same publication is then rejected (same version). So statements of the form "a voter in term $t$ has either acknowledged or can still accept" (`publication_acks_accepted`), or "once the votes are counted, a commit was sent" (`publication_committed`), hold for the model. In OpenSearch they presuppose that remote writes succeed.

## Docstrings versus terms

- **Module docstring.** It says a stable period is one in which "one node runs for election (or publishes) and nothing disrupts it, while every other step of the cluster remains possible — deliveries in any order, duplicates, other nodes' joins, acceptances and commits, restarts of other nodes". In the terms:
  - The election period also forbids every new publication by *any* node. It forbids any start-join anywhere to a term $\ge t$ other than handling $c$'s request for $t$; this applies to nodes outside $Q$ too, so no third node can start an election at a term $\ge t$. It forbids bootstraps of $c$ and $Q$, and acceptance by $c$ or $Q$ of publications fresher than $(k_t, k_v)$.
  - The publication period forbids start-joins above $t$ only at $c$ and $Q$, further publications by $c$, and restarts of $c$.

  These exclusions are the ones listed in the step docstrings, so "every other step" must be read relative to them. The docstring also says that the theorems show "the steps the protocol needs stay enabled". The theorems state enabledness only for three steps:
  - $c$ handling a voter's term-$t$ join;
  - a voter that is already in term $t$ handling the publication;
  - $c$ handling a voter's acknowledgement.

  No theorem states that the start-joins needed along the way stay enabled: $c$'s own start-join to $t$, a voter handling $c$'s request, and a member of $Q$ moving up to term $t$ in a publication period. The period definitions allow these steps, and the handler's only guard is the term comparison, so this is a gap in what is stated rather than a contradiction.
- **`ElectionStep` docstring.** It is consistent with the term: start-joins in a term $\ge t$ other than $c$'s request for $t$ are excluded; new publications are excluded; bootstrap and restart of $c$ or a voter are excluded; and acceptance by $c$ or a voter of a publication with a key above $(k_t, k_v)$ is excluded. There is one nuance. "Restart of $c$ or of a voter" is excluded only for the `restart` constructor (eligible nodes); `restartAny` (non-eligible nodes) is not guarded by node identity. This matters only if $c$ or a voter is non-eligible, which the election theorems rule out with `hc` and `hQ`.
- **`ElectionExec` docstring** ("finite sequences of `ElectionStep`s"). Consistent, and it includes the empty sequence.
- **`PublicationStep` docstring.** Consistent: start-joins above $t$ at $c$ or $Q$, a further publication by $c$, and a restart of $c$ are excluded. The same `restartAny` nuance applies to $c$. The publication theorems do not assume $c$ eligible, but in a reachable cluster $\mathrm{won}(c) = \mathrm{true}$ implies it (G3).
- **`PublicationExec` docstring.** Consistent.
