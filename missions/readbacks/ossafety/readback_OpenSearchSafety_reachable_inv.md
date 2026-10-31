# Read-back: `OpenSearchSafety.reachable_inv`

## Notions used

**Sources and conventions.** Rendered from `Definitions/Def_OpenSearchCoordination.lean`, `Definitions/Def_OpenSearchSafety.lean` and the stub `Theorems/Thm_OpenSearchSafety_reachable_inv.lean`; Java line numbers refer to OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19` (CS = `CoordinationState.java`, CM = `CoordinationMetadata.java`, ES = `ElectionStrategy.java`, CO = `Coordinator.java`, CBS = `ClusterBootstrapService.java`), checked against the local checkout. Throughout, $V$ is an arbitrary payload type, $P$ a parameter record and $W$ a cluster; $cs_n$ abbreviates $W.\mathrm{node}(n)$, the coordination state of node $n$ in $W$, and "$m \in \mathrm{sent}$" means $W.\mathrm{sent}(m)$. Booleans are read as truth values: "$\mathrm{won}(cs)$" means `electionWon = true`, "$\neg\mathrm{won}(cs)$" means `electionWon = false`.

**Nodes, configurations, quorums.** Node ids are natural numbers. A *discovery node* $d$ is a pair $(d.\mathrm{id}, d.\mathrm{cm})$ of an id and a Boolean (`isClusterManagerNode`). A *voting configuration* $c$ is a strictly increasing list of node ids, hence duplicate-free; two configurations are equal exactly when they have the same members. $\emptyset$ denotes the empty configuration `EMPTY_CONFIG`; "$c$ is empty" means its list is empty. For a configuration $c$ and any list $q$ of ids,
$$\mathrm{hasQuorum}(c, q) \iff 2\cdot\big|\{x \in c : x \in q\}\big| > |c| ,$$
so the empty configuration has no quorum, and ids of $q$ outside $c$ as well as repetitions in $q$ are irrelevant. *Transcription check:* matches `VotingConfiguration.hasQuorum` (CM:405-409).

A *vote collection* is a list of node ids; the empty collection is $[\,]$; $\mathrm{isQuorum}(v, c) := \mathrm{hasQuorum}(c, v)$; $\mathrm{addVote}(v, d)$ is $(d.\mathrm{id} :: v,\ \text{added})$ if $d.\mathrm{cm}$ is true and $d.\mathrm{id} \notin v$, and $(v,\ \text{not added})$ otherwise. *Transcription check:* `VoteCollection` (CS:750-814) keys a map by node id; `addVote` (CS:755-757) changes the key set exactly in the same cases.

**Cluster states.** A cluster state $s$ has a term $s.\mathrm{term} \in \mathbb{N}$, a version $s.\mathrm{version} \in \mathbb{Z}$, a metadata version $s.\mathrm{mv} \in \mathbb{Z}$, a last committed and a last accepted configuration $s.\mathrm{lcc}$ and $s.\mathrm{lac}$, an optional natural number $s.\mathrm{cmNode}$ (the cluster-manager node), two Booleans $s.\mathrm{uuidKnown}$ and $s.\mathrm{uuidCommitted}$, and a payload $s.\mathrm{value} \in V$. Two cluster states are equal when all nine fields are. $\mathrm{vomv}(s)$ (`versionOrMetadataVersion`) is $s.\mathrm{mv}$ if $s.\mathrm{term} = 0$ and $s.\mathrm{version}$ otherwise. $\mathrm{markCommitted}(s)$ is $s$ with $\mathrm{lcc}$ replaced by $s.\mathrm{lac}$ and with $\mathrm{uuidCommitted}$ set to true when $s.\mathrm{uuidKnown}$ is true; nothing else changes (transcribes CS:703-740; the Java assertion at CS:708-710 is not checked).

**Message contents.** A *join* $j$ has a source and a target discovery node $j.\mathrm{src}$, $j.\mathrm{tgt}$, a term $j.\mathrm{term} \in \mathbb{N}$, a last accepted term $j.\mathrm{lat} \in \mathbb{N}$ and a last accepted version $j.\mathrm{lav} \in \mathbb{Z}$; two joins are equal when all five fields are. A *publish response* is a pair $\langle t, v\rangle \in \mathbb{N}\times\mathbb{Z}$. An *apply-commit request* is a triple $\langle d, t, v\rangle$ of a discovery node, a term and a version. A *start-join request* is a pair of a discovery node and a term; it is not a cluster message (see the steps).

**Coordination states.** A coordination state $cs$ has a local node $cs.\mathrm{localNode}$ (a discovery node), a current term $\mathrm{ct}(cs) \in \mathbb{N}$, a last accepted state $cs.\mathrm{las}$ (a cluster state), two vote collections $\mathrm{joinVotes}(cs)$ and $\mathrm{pubVotes}(cs)$, Booleans $\mathrm{started}(cs)$ (`startedJoinSinceLastReboot`) and $\mathrm{won}(cs)$ (`electionWon`), a last published version $\mathrm{lpv}(cs) \in \mathbb{Z}$ and a last published configuration $\mathrm{lpc}(cs)$. $\mathrm{lat}(cs)$, $\mathrm{lav}(cs)$, $\mathrm{lcc}(cs)$, $\mathrm{lac}(cs)$ are the term, version, last committed and last accepted configuration of $cs.\mathrm{las}$. $\mathrm{init}(d, t, s)$ is the coordination state with local node $d$, current term $t$, last accepted state $s$, both vote collections empty, $\mathrm{started}$ and $\mathrm{won}$ false, $\mathrm{lpv} = 0$ and $\mathrm{lpc} = s.\mathrm{lac}$ (the constructor, CS:84-106).

**Election strategies.** An election strategy is a Boolean function $\sigma(d, t, at, av, c_1, c_2, v)$ of a discovery node, two naturals, an integer, two configurations and a vote collection; `DEFAULT_INSTANCE` is the constant-true function. $\mathrm{isElectionQuorum}_\sigma(cs, v) := \mathrm{isQuorum}(v, \mathrm{lcc}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{lac}(cs)) \wedge \sigma(cs.\mathrm{localNode}, \mathrm{ct}(cs), \mathrm{lat}(cs), \mathrm{lav}(cs), \mathrm{lcc}(cs), \mathrm{lac}(cs), v)$; for the default strategy the third conjunct is true. $\mathrm{isPublishQuorum}(cs, v) := \mathrm{isQuorum}(v, \mathrm{lcc}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{lpc}(cs))$. *Transcription check:* ES:68-88 with CS:144-154, and CS:156-158.

**Parameters.** A parameter record $P$ consists of $\mathrm{elig} : \mathbb{N} \to \mathrm{Bool}$ (`eligible`: whether a node is cluster-manager-eligible), a predicate $\mathrm{initConfs}$ on configurations (an arbitrary set of "bootstrap configurations": possibly empty, possibly containing $\emptyset$, possibly infinite), and an election strategy $\sigma_P$ (`strategy`). $\mathrm{dn}(n) := (n, \mathrm{elig}(n))$; "$x$ is eligible" means $\mathrm{elig}(x) = $ true. $\mathrm{InitCompatible}(P)$ holds when for all configurations $X, Y$ with $\mathrm{initConfs}(X)$ and $\mathrm{initConfs}(Y)$ and all lists $q_1, q_2$ of eligible ids,
$$\mathrm{hasQuorum}(X, q_1) \wedge \mathrm{hasQuorum}(Y, q_2) \implies \exists x,\ x \in q_1 \wedge x \in q_2$$
(for $X = Y$ this is automatic: two majorities of one configuration meet).

**Messages and clusters.** A cluster message is one of: $\mathsf{join}(j)$; $\mathsf{pubReq}(a, s, pt, pv)$, a publish request from node $a$ carrying a cluster state $s$ and a *ghost parent* $(pt, pv) \in \mathbb{N}\times\mathbb{Z}$; $\mathsf{pubResp}(a, d, r)$, a publish response $r$ from node $a$ to node $d$; $\mathsf{commit}(c)$, an apply-commit request $c$. A cluster $W$ is a function $W.\mathrm{node}$ from node ids to coordination states together with a predicate $W.\mathrm{sent}$ on messages (the messages sent so far). $W.\mathrm{set}(n, cs)$ replaces node $n$'s state by $cs$ and changes nothing else; $W.\mathrm{send}(m)$ adds $m$ to the sent set and changes nothing else. A *key* is a pair $(t, v) \in \mathbb{N}\times\mathbb{Z}$; the key of a publication $\mathsf{pubReq}(a, s, pt, pv)$ is $(s.\mathrm{term}, s.\mathrm{version})$.

**The handlers.** Each handler returns either an error (the corresponding step is then impossible) or a result. Guards are tested in the order listed; the first that applies gives the error.

- $\mathrm{setInitialState}(cs, s)$: error if $\mathrm{lac}(cs)$ is non-empty; otherwise $cs$ with $cs.\mathrm{las} := s$ (nothing else changes). Its *contract* $\mathrm{initialStateContract}(cs, s)$ is the conjunction: $\mathrm{lat}(cs) = 0$; $\mathrm{lcc}(cs)$ empty; $\mathrm{lpv}(cs) = 0$; $\mathrm{lpc}(cs)$ empty; $\neg\mathrm{won}(cs)$; $\mathrm{joinVotes}(cs)$ and $\mathrm{pubVotes}(cs)$ empty; $s.\mathrm{term} = 0$; $s.\mathrm{version} = \mathrm{lav}(cs)$; $s.\mathrm{lac}$ and $s.\mathrm{lcc}$ non-empty. *Transcription check:* CS:180-204; the contract is the eleven assertions CS:190-201.
- $\mathrm{handleStartJoin}(cs, (d, t))$: error if $t \le \mathrm{ct}(cs)$; otherwise the pair of $cs$ with $\mathrm{ct} := t$, $\mathrm{lpv} := 0$, $\mathrm{lpc} := \mathrm{lac}(cs)$, $\mathrm{started} :=$ true, $\mathrm{won} :=$ false and both vote collections emptied (last accepted state unchanged), and the join $\langle cs.\mathrm{localNode}, d, t, \mathrm{lat}(cs), \mathrm{vomv}(cs.\mathrm{las})\rangle$ (source, target, term, last accepted term, last accepted version — the metadata version when $\mathrm{lat}(cs) = 0$). *Transcription check:* CS:213-255.
- $\mathrm{handleJoin}_\sigma(cs, j)$: errors, in order, if $j.\mathrm{term} \ne \mathrm{ct}(cs)$; if $\neg\mathrm{started}(cs)$; if $j.\mathrm{lat} > \mathrm{lat}(cs)$; if $j.\mathrm{lat} = \mathrm{lat}(cs)$ and $j.\mathrm{lav} > \mathrm{vomv}(cs.\mathrm{las})$; if $\mathrm{lac}(cs)$ is empty. Otherwise, with $(v', b) = \mathrm{addVote}(\mathrm{joinVotes}(cs), j.\mathrm{src})$ and $w = \mathrm{isElectionQuorum}_\sigma(cs, v')$, the result is $cs$ with $\mathrm{joinVotes} := v'$ and $\mathrm{won} := w$, and moreover $\mathrm{lpv} := \mathrm{lav}(cs)$ if $w$ holds and $\mathrm{won}(cs)$ did not; together with the Boolean $b$ ("vote added"). The target $j.\mathrm{tgt}$ is not examined. *Transcription check:* CS:264-339; the Java assertions CS:265 (target is the local node) and CS:323-324 (a won election is not lost) are not checked by the handler.
- $\mathrm{handleClientValue}(cs, s)$: errors, in order, if $\neg\mathrm{won}(cs)$; if $\mathrm{lpv}(cs) \ne \mathrm{lav}(cs)$; if $s.\mathrm{term} \ne \mathrm{ct}(cs)$; if $s.\mathrm{version} \le \mathrm{lpv}(cs)$; if $s.\mathrm{lac} \ne \mathrm{lac}(cs)$ and $\mathrm{lcc}(cs) \ne \mathrm{lac}(cs)$; if $\neg\mathrm{isQuorum}(\mathrm{joinVotes}(cs), s.\mathrm{lac})$. Otherwise $cs$ with $\mathrm{lpv} := s.\mathrm{version}$, $\mathrm{lpc} := s.\mathrm{lac}$, $\mathrm{pubVotes} := [\,]$, together with the publish request carrying $s$. Its *contract* $\mathrm{clientValueContract}(cs, s)$ is $s.\mathrm{lcc} = \mathrm{lcc}(cs)$. *Transcription check:* CS:348-407; the contract is the assertion CS:397-398.
- $\mathrm{handlePublishRequest}(cs, s)$: error if $s.\mathrm{term} \ne \mathrm{ct}(cs)$. Otherwise, if $s.\mathrm{term} = \mathrm{lat}(cs)$ and $s.\mathrm{version} \le \mathrm{lav}(cs)$: when $s.\mathrm{term} \ne 0$, error; when $s.\mathrm{term} = 0$ (the "Zen1" branch), error if $s.\mathrm{cmNode}$ is none, *accept* if $s.\mathrm{cmNode} = \mathrm{some}\ m$ with $\mathrm{some}\ m \ne cs.\mathrm{las}.\mathrm{cmNode}$, error otherwise. In all remaining cases, *accept*. To accept is to return $cs$ with $cs.\mathrm{las} := s$ and the response $\langle s.\mathrm{term}, s.\mathrm{version}\rangle$. *Transcription check:* CS:416-460 (a null incoming cluster-manager in the Zen1 branch throws in Java).
- $\mathrm{handlePublishResponse}(cs, d, r)$: errors, in order, if $\neg\mathrm{won}(cs)$; if $r.\mathrm{term} \ne \mathrm{ct}(cs)$; if $r.\mathrm{version} \ne \mathrm{lpv}(cs)$. Otherwise let $v'$ be the collection returned by $\mathrm{addVote}(\mathrm{pubVotes}(cs), d)$; the result is $cs$ with $\mathrm{pubVotes} := v'$, together with the optional apply-commit request $\mathrm{some}\ \langle cs.\mathrm{localNode}, r.\mathrm{term}, r.\mathrm{version}\rangle$ if $\mathrm{isQuorum}(v', \mathrm{lcc}(cs)) \wedge \mathrm{isQuorum}(v', \mathrm{lpc}(cs))$, and $\mathrm{none}$ otherwise. *Transcription check:* CS:471-515.
- $\mathrm{handleCommit}(cs, \langle d, t, v\rangle)$: errors, in order, if $t \ne \mathrm{ct}(cs)$; if $t \ne \mathrm{lat}(cs)$; if $v \ne \mathrm{lav}(cs)$. Otherwise $cs$ with $cs.\mathrm{las} := \mathrm{markCommitted}(cs.\mathrm{las})$. The source $d$ is not examined. *Transcription check:* CS:523-573.

**Restart states.** $\mathrm{RestartState}(s, s')$ holds when either (i) $s'$ agrees with $s$ on term, version, $\mathrm{lcc}$, $\mathrm{lac}$, $\mathrm{uuidKnown}$ and $\mathrm{uuidCommitted}$ (its metadata version, cluster-manager node and payload are free); or (ii) $s.\mathrm{term} = 0$, $s.\mathrm{lcc} = s.\mathrm{lac} = \emptyset$, $s.\mathrm{uuidKnown} =$ false, and $s'.\mathrm{term} = 0$, $s'.\mathrm{lcc} = s'.\mathrm{lac} = \emptyset$ (every other field of $s'$, including its version, is free). *Citation check:* in `GatewayMetaState.java` (141-207) an eligible node reloads its persisted current term, version and metadata (the metadata includes the coordination metadata and the cluster-UUID flags). The remote-store path (169-186) is taken by an eligible node with remote cluster state enabled when its local cluster UUID is unknown and the remote store knows one; the restored state is built on `Metadata.EMPTY_METADATA` (line 296), to which `RemoteStoreRestoreService.restore` adds index metadata, global settings, templates, customs and the remote version, but no coordination metadata and no cluster UUID — so its term is 0 and its configurations are empty, as in (ii). Java also persists the rest of the metadata (payload, metadata version), which (i) leaves free: more behaviours than Java.

**Initial clusters.** $\mathrm{Initial}(P, W)$ holds when every node $n$ has $cs_n = \mathrm{init}(\mathrm{dn}(n), 0, s_n)$ for some cluster state $s_n$ with $s_n.\mathrm{term} = 0$ and $s_n.\mathrm{lcc} = s_n.\mathrm{lac} = \emptyset$ (the version, metadata version, cluster-manager node, cluster-UUID flags and payload of $s_n$ are arbitrary and may differ from node to node), and no message is sent.

**Steps.** $\mathrm{Step}_P(W, W')$ holds exactly in the following nine cases (all objects arbitrary unless constrained):

1. *bootstrap*: a node $n$, a configuration $X$ with $\mathrm{initConfs}(X)$, a cluster state $s$ with $\mathrm{initialStateContract}(cs_n, s)$ and $s.\mathrm{lcc} = s.\mathrm{lac} = X$, and $\mathrm{setInitialState}(cs_n, s) = \mathrm{ok}\ cs'$; then $W' = W.\mathrm{set}(n, cs')$. Node $n$ need not be eligible (the Coordinator rejects non-eligible nodes and imposes further guards, CO:1110-1141; omitting them only adds behaviours).
2. *startJoin*: nodes $n$, $src$ with $src$ eligible, a term $t$, and $\mathrm{handleStartJoin}(cs_n, (\mathrm{dn}(src), t)) = \mathrm{ok}\ (cs', j)$; then $W' = W.\mathrm{set}(n, cs').\mathrm{send}(\mathsf{join}(j))$. No message from $src$ is required.
3. *join*: a node $n$ and a join $j$ with $\mathsf{join}(j) \in \mathrm{sent}$, $j.\mathrm{tgt}.\mathrm{id} = n$ and $\mathrm{handleJoin}_{\sigma_P}(cs_n, j) = \mathrm{ok}\ (cs', b)$; then $W' = W.\mathrm{set}(n, cs')$.
4. *clientValue*: a node $n$ and a cluster state $s$ with $\mathrm{clientValueContract}(cs_n, s)$ and $\mathrm{handleClientValue}(cs_n, s) = \mathrm{ok}\ (cs', p)$; then $W' = W.\mathrm{set}(n, cs').\mathrm{send}(\mathsf{pubReq}(n, s, \mathrm{lat}(cs_n), \mathrm{lav}(cs_n)))$: the request carries the state of $p$, which is $s$, and as ghost parent the key of $n$'s last accepted state (unchanged by the handler).
5. *publish*: nodes $n$, $src$ and $\mathsf{pubReq}(src, s, pt, pv) \in \mathrm{sent}$ with $\mathrm{handlePublishRequest}(cs_n, s) = \mathrm{ok}\ (cs', r)$; then $W' = W.\mathrm{set}(n, cs').\mathrm{send}(\mathsf{pubResp}(n, src, r))$. Any node may handle any sent publish request.
6. *respond*: nodes $n$, $src$ and $\mathsf{pubResp}(src, n, r) \in \mathrm{sent}$ with $\mathrm{handlePublishResponse}(cs_n, \mathrm{dn}(src), r) = \mathrm{ok}\ (cs', o)$; then $W' = W.\mathrm{set}(n, cs')$ if $o = \mathrm{none}$ and $W' = W.\mathrm{set}(n, cs').\mathrm{send}(\mathsf{commit}(c))$ if $o = \mathrm{some}\ c$.
7. *commit*: a node $n$ and $\mathsf{commit}(c) \in \mathrm{sent}$ with $\mathrm{handleCommit}(cs_n, c) = \mathrm{ok}\ cs'$; then $W' = W.\mathrm{set}(n, cs')$. Any node may handle any sent commit.
8. *restart*: an eligible node $n$ and a cluster state $s'$ with $\mathrm{RestartState}(cs_n.\mathrm{las}, s')$; then $W' = W.\mathrm{set}(n, \mathrm{init}(cs_n.\mathrm{localNode}, \mathrm{ct}(cs_n), s'))$.
9. *restartAny*: a node $n$ that is not eligible, any term $t$ and any cluster state $s'$; then $W' = W.\mathrm{set}(n, \mathrm{init}(cs_n.\mathrm{localNode}, t, s'))$.

Messages are never removed from the sent set; a sent message may be handled any number of times, or never.

**Reachability.** $\mathrm{Reachable}_P$ is the least predicate on clusters that holds of every $W$ with $\mathrm{Initial}(P, W)$ and holds of $W'$ whenever it holds of $W$ and $\mathrm{Step}_P(W, W')$.

**Commits.** $\mathrm{Committed}(W, t, v)$ holds when $\mathsf{commit}(\langle d, t, v\rangle) \in \mathrm{sent}$ for some discovery node $d$ (the source is irrelevant).

**Descent.** $\mathrm{Parent}(W, (t, v), (t', v'))$ holds when some $\mathsf{pubReq}(a, s, t, v) \in \mathrm{sent}$ has $s.\mathrm{term} = t'$ and $s.\mathrm{version} = v'$: a publication of key $(t', v')$ was sent with ghost parent $(t, v)$. $\mathrm{Descends}(W, k, k')$, for keys $k, k'$, is the least relation that holds when $k' = k$ — for every key, whether or not anything was published under it — and that holds of $(k, k'')$ whenever it holds of $(k, k')$ and $\mathrm{Parent}(W, k', k'')$. Thus $\mathrm{Descends}(W, k, k')$ means: $k = k'$, or there is a chain $k = k_0, k_1, \dots, k_m = k'$ with $m \ge 1$ and $\mathrm{Parent}(W, k_{i-1}, k_i)$ for each $i$. Descent relates keys through ghost parents only; it says nothing about the payloads of the states.

**Auxiliary notions of the invariant.**
- $\mathrm{KeyLE}((t, v), (t', v'))$: $t < t'$, or $t = t'$ and $v \le v'$.
- $\mathrm{Below}((lt, lv), (bt, bv))$: $lt < bt$, or $lt = bt$ and ($bt = 0$ or $lv \le bv$) — at term $0$ versions are not compared.
- $\mathrm{Realizes}(P, W, (t, v), x, y)$: either $t = 0$, $x = y$ and $\mathrm{initConfs}(x)$ (with $v$ unconstrained); or some $\mathsf{pubReq}(a, s, pt, pv) \in \mathrm{sent}$ has $s.\mathrm{term} = t$, $s.\mathrm{version} = v$, $y = s.\mathrm{lac}$, and either $x = s.\mathrm{lcc}$, or $x = s.\mathrm{lac}$ and $\mathrm{Committed}(W, t, v)$.
- $\mathrm{JoinVoters}(P, W, L, t, J)$: every $x \in J$ is eligible and some $\mathsf{join}(j) \in \mathrm{sent}$ has $j.\mathrm{src}.\mathrm{id} = x$, $j.\mathrm{tgt}.\mathrm{id} = L$ and $j.\mathrm{term} = t$.
- $\mathrm{BaseVoters}(P, W, L, t, (bt, bv), J)$: the same, the witnessing join satisfying in addition $\mathrm{Below}((j.\mathrm{lat}, j.\mathrm{lav}), (bt, bv))$.
- $\mathrm{RespVoters}(P, W, (t, v), A)$: every $x \in A$ is eligible and $\mathsf{pubResp}(x, d, \langle t, v\rangle) \in \mathrm{sent}$ for some $d$.
- $\mathrm{ElectionRecord}(P, W, L, t, (bt, bv), x, y, J)$: $bt < t$, $\mathrm{Realizes}(P, W, (bt, bv), x, y)$, $\mathrm{BaseVoters}(P, W, L, t, (bt, bv), J)$, $\mathrm{hasQuorum}(x, J)$ and $\mathrm{hasQuorum}(y, J)$.
- $\mathrm{Won}(P, W, b, t)$: $b$ is eligible, and either ($\mathrm{won}(cs_b)$ and $\mathrm{ct}(cs_b) = t$) or some $\mathsf{pubReq}(b, s, pt, pv) \in \mathrm{sent}$ has $s.\mathrm{term} = t$.

**The invariant.** $\mathrm{Inv}(P, W)$ is the conjunction of the following 30 statements (Lean field names in parentheses); nodes $n, m, a, b, d$ range over all node ids, $j, j'$ over all joins, $r$ over all publish responses.

*Every node $n$:*
1. (`localNode_eq`) $cs_n.\mathrm{localNode} = \mathrm{dn}(n)$.
2. (`idle_of_not_won`) $\neg\mathrm{won}(cs_n) \Rightarrow \mathrm{lpv}(cs_n) = 0 \wedge \mathrm{pubVotes}(cs_n) = [\,]$.
3. (`won_started`) $\mathrm{won}(cs_n) \Rightarrow \mathrm{started}(cs_n)$.
4. (`votes_started`) $\mathrm{joinVotes}(cs_n) \ne [\,] \Rightarrow \mathrm{started}(cs_n)$.
5. (`started_term_pos`) $\mathrm{started}(cs_n) \Rightarrow \mathrm{ct}(cs_n) \ge 1$.
6. (`won_quorum`) $\mathrm{won}(cs_n) \Rightarrow \mathrm{isQuorum}(\mathrm{joinVotes}(cs_n), \mathrm{lcc}(cs_n)) \wedge \mathrm{isQuorum}(\mathrm{joinVotes}(cs_n), \mathrm{lac}(cs_n))$.
7. (`not_won_no_quorum`) $\neg\mathrm{won}(cs_n) \Rightarrow \neg\big(\mathrm{isQuorum}(\mathrm{joinVotes}(cs_n), \mathrm{lcc}(cs_n)) \wedge \mathrm{isQuorum}(\mathrm{joinVotes}(cs_n), \mathrm{lac}(cs_n))\big)$.
8. (`joinVotes_sent`) every $m \in \mathrm{joinVotes}(cs_n)$ is eligible, and some $\mathsf{join}(j) \in \mathrm{sent}$ has $j.\mathrm{src}.\mathrm{id} = m$, $j.\mathrm{tgt}.\mathrm{id} = n$, $j.\mathrm{term} = \mathrm{ct}(cs_n)$ and $\mathrm{Below}((j.\mathrm{lat}, j.\mathrm{lav}), (\mathrm{lat}(cs_n), \mathrm{lav}(cs_n)))$.
9. (`publishVotes_sent`) every $m \in \mathrm{pubVotes}(cs_n)$ is eligible and $\mathsf{pubResp}(m, n, \langle \mathrm{ct}(cs_n), \mathrm{lpv}(cs_n)\rangle) \in \mathrm{sent}$.

*Every eligible node $n$:*

10. (`term_le`) $\mathrm{lat}(cs_n) \le \mathrm{ct}(cs_n)$.
11. (`accepted_realizes`) $\big(\mathrm{lat}(cs_n) = 0 \wedge \mathrm{lcc}(cs_n) = \emptyset \wedge \mathrm{lac}(cs_n) = \emptyset\big) \vee \mathrm{Realizes}(P, W, (\mathrm{lat}(cs_n), \mathrm{lav}(cs_n)), \mathrm{lcc}(cs_n), \mathrm{lac}(cs_n))$.

*Joins and publish responses:*

12. (`join_wf`) if $\mathsf{join}(j) \in \mathrm{sent}$ then $j.\mathrm{src} = \mathrm{dn}(j.\mathrm{src}.\mathrm{id})$ and $j.\mathrm{tgt}.\mathrm{id}$ is eligible.
13. (`join_term_le`) if $\mathsf{join}(j) \in \mathrm{sent}$ and $j.\mathrm{src}.\mathrm{id}$ is eligible then $j.\mathrm{term} \le \mathrm{ct}(cs_{j.\mathrm{src}.\mathrm{id}})$.
14. (`join_unique`) if $\mathsf{join}(j), \mathsf{join}(j') \in \mathrm{sent}$, $j.\mathrm{src}.\mathrm{id}$ is eligible, $j.\mathrm{src}.\mathrm{id} = j'.\mathrm{src}.\mathrm{id}$ and $j.\mathrm{term} = j'.\mathrm{term}$, then $j = j'$ (all five fields, in particular the same target).
15. (`join_after_response`) if $\mathsf{join}(j) \in \mathrm{sent}$, $\mathsf{pubResp}(a, d, r) \in \mathrm{sent}$, $j.\mathrm{src}.\mathrm{id} = a$, $a$ is eligible and $r.\mathrm{term} < j.\mathrm{term}$, then $\mathrm{KeyLE}((r.\mathrm{term}, r.\mathrm{version}), (j.\mathrm{lat}, j.\mathrm{lav}))$.
16. (`response_le`) if $\mathsf{pubResp}(a, d, r) \in \mathrm{sent}$ and $a$ is eligible, then $r.\mathrm{term} \le \mathrm{ct}(cs_a)$ and $\mathrm{KeyLE}((r.\mathrm{term}, r.\mathrm{version}), (\mathrm{lat}(cs_a), \mathrm{lav}(cs_a)))$.
17. (`response_published`) if $\mathsf{pubResp}(a, d, r) \in \mathrm{sent}$ then some $\mathsf{pubReq}(d, s, pt, pv) \in \mathrm{sent}$ — sent by the addressee $d$ — has $s.\mathrm{term} = r.\mathrm{term}$ and $s.\mathrm{version} = r.\mathrm{version}$.

*Publications: for every $\mathsf{pubReq}(a, s, pt, pv) \in \mathrm{sent}$:*

18. (`pub_wf`) $a$ is eligible, $s.\mathrm{term} \ge 1$, $pt \le s.\mathrm{term}$, $pv < s.\mathrm{version}$, and $pt = 0 \Rightarrow \mathrm{initConfs}(s.\mathrm{lcc})$.
19. (`pub_parent`) if $pt \ge 1$, some $\mathsf{pubReq}(a', s', pt', pv') \in \mathrm{sent}$ has $s'.\mathrm{term} = pt$, $s'.\mathrm{version} = pv$, [$s.\mathrm{lcc} = s'.\mathrm{lcc}$, or $s.\mathrm{lcc} = s'.\mathrm{lac}$ and $\mathrm{Committed}(W, pt, pv)$], and [$s.\mathrm{lac} \ne s'.\mathrm{lac} \Rightarrow s.\mathrm{lcc} = s'.\mathrm{lac}$].
20. (`pub_unique`) every $\mathsf{pubReq}(a', s', pt', pv') \in \mathrm{sent}$ with $s'.\mathrm{term} = s.\mathrm{term}$ and $s'.\mathrm{version} = s.\mathrm{version}$ has $a' = a$, $s' = s$, $pt' = pt$ and $pv' = pv$.
21. (`pub_rooted`) $\mathrm{Descends}(W, (0, v_0), (s.\mathrm{term}, s.\mathrm{version}))$ for some $v_0 \in \mathbb{Z}$.
22. (`pub_same_term`) every $\mathsf{pubReq}(a', s', pt', pv') \in \mathrm{sent}$ with $s'.\mathrm{term} = s.\mathrm{term}$ has $\mathrm{Descends}(W, (s.\mathrm{term}, s.\mathrm{version}), (s'.\mathrm{term}, s'.\mathrm{version}))$ or the converse.
23. (`pub_voters`) some list $J$ has $\mathrm{JoinVoters}(P, W, a, s.\mathrm{term}, J)$, $\mathrm{hasQuorum}(s.\mathrm{lcc}, J)$ and $\mathrm{hasQuorum}(s.\mathrm{lac}, J)$.
24. (`pub_election`) if $pt < s.\mathrm{term}$, some $y$ and $J$ have $\mathrm{ElectionRecord}(P, W, a, s.\mathrm{term}, (pt, pv), s.\mathrm{lcc}, y, J)$.

*Commits:*

25. (`commit_quorum`) for every $\mathsf{commit}(\langle d, t, v\rangle) \in \mathrm{sent}$, some $\mathsf{pubReq}(a, s, pt, pv) \in \mathrm{sent}$ has $s.\mathrm{term} = t$ and $s.\mathrm{version} = v$, and some list $A$ has $\mathrm{RespVoters}(P, W, (t, v), A)$, $\mathrm{hasQuorum}(s.\mathrm{lac}, A)$, and either $\mathrm{hasQuorum}(s.\mathrm{lcc}, A)$, or [$\mathrm{Committed}(W, pt, pv)$ and some $\mathsf{pubReq}(a', s', pt', pv') \in \mathrm{sent}$ has $s'.\mathrm{term} = pt$, $s'.\mathrm{version} = pv$, $s'.\mathrm{lac} = s.\mathrm{lac}$].

*Leaders:*

26. (`won_unique`) $\mathrm{Won}(P, W, a, t) \wedge \mathrm{Won}(P, W, b, t) \Rightarrow a = b$.
27. (`pub_source_term`) for every $\mathsf{pubReq}(a, s, pt, pv) \in \mathrm{sent}$: $s.\mathrm{term} < \mathrm{ct}(cs_a)$, or $s.\mathrm{term} = \mathrm{ct}(cs_a)$ and ($\mathrm{won}(cs_a)$ or $\neg\mathrm{started}(cs_a)$).
28. (`leader_pubs`) if $\mathrm{won}(cs_n)$, every $\mathsf{pubReq}(a, s, pt, pv) \in \mathrm{sent}$ with $s.\mathrm{term} = \mathrm{ct}(cs_n)$, whoever its sender $a$, has $s.\mathrm{version} \le \mathrm{lpv}(cs_n)$, $\mathrm{Descends}(W, (s.\mathrm{term}, s.\mathrm{version}), (\mathrm{ct}(cs_n), \mathrm{lpv}(cs_n)))$, $\mathrm{isQuorum}(\mathrm{joinVotes}(cs_n), s.\mathrm{lcc})$ and $\mathrm{isQuorum}(\mathrm{joinVotes}(cs_n), s.\mathrm{lac})$.
29. (`leader_inflight`) if $\mathrm{won}(cs_n)$ and $\mathrm{lpv}(cs_n) \ne \mathrm{lav}(cs_n)$, some $s$ has $\mathsf{pubReq}(n, s, \mathrm{lat}(cs_n), \mathrm{lav}(cs_n)) \in \mathrm{sent}$, $s.\mathrm{term} = \mathrm{ct}(cs_n)$, $s.\mathrm{version} = \mathrm{lpv}(cs_n)$, $\mathrm{lpc}(cs_n) = s.\mathrm{lac}$, and either $\mathrm{lcc}(cs_n) = s.\mathrm{lcc}$, or [$\mathrm{lcc}(cs_n) = s.\mathrm{lac}$, $\mathrm{Committed}(W, \mathrm{lat}(cs_n), \mathrm{lav}(cs_n))$ and $\mathrm{lac}(cs_n) = s.\mathrm{lac}$].
30. (`leader_settled`) if $\mathrm{won}(cs_n)$ and $\mathrm{lpv}(cs_n) = \mathrm{lav}(cs_n)$: either $\mathrm{lat}(cs_n) = \mathrm{ct}(cs_n)$ and $\mathrm{lpc}(cs_n) = \mathrm{lac}(cs_n)$, or $\mathrm{lat}(cs_n) < \mathrm{ct}(cs_n)$ and no $\mathsf{pubReq}(a, s, pt, pv) \in \mathrm{sent}$ has $s.\mathrm{term} = \mathrm{ct}(cs_n)$.

*Docstring remarks.* The docstring of `idle_of_not_won` says that a node that has not won "has published nothing in its term"; the term only says $\mathrm{lpv} = 0$ and no publish votes, which a node that published in its current term and then restarted also satisfies. The docstring of `leader_pubs` speaks of "an elected node's publications of its term"; the term covers every publication of that term, whoever sent it (a stronger statement).


## 1. Declaration

**Binders and hypotheses**, in order:

1. an implicit payload type $V$ and a parameter record $P$;
2. `hP` : $\mathrm{InitCompatible}(P)$;
3. `hes` : $\sigma_P =$ `DEFAULT_INSTANCE`;
4. a cluster $W$ and `hW` : $\mathrm{Reachable}_P(W)$.

**Conclusion.** $\mathrm{Inv}(P, W)$: all thirty conjuncts above hold in every reachable cluster.

## 2. What is not constrained

- $\mathrm{elig}$ and $\mathrm{initConfs}$ are arbitrary apart from $\mathrm{InitCompatible}(P)$; the payload type $V$ is arbitrary. Only the default election strategy is covered.
- Reachable clusters include every interleaving of the nine steps: messages lost, duplicated, delayed and reordered; crashes and restarts at any time; start-joins from any eligible node with any higher term; any client value the handlers accept.
- The statement asserts only the conclusion; that it follows from `inv_init` and the nine step lemmas by induction on $\mathrm{Reachable}_P$ is not part of it.
- Not vacuous: reachable clusters with publications and commits exist (the one-node scenario in the read-back of `commit_reachable`).

## 3. Plain-language summary

In every cluster reachable from a fresh one, the thirty-part invariant holds — when the bootstrap configurations are pairwise compatible and the default election strategy is used.
