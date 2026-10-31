# Read-back: `OpenSearchSafety.inv_bootstrap`

## Notions used

**Sources and conventions.** Rendered from `Definitions/Def_OpenSearchCoordination.lean`, `Definitions/Def_OpenSearchSafety.lean` and the stub `Theorems/Thm_OpenSearchSafety_inv_bootstrap.lean`; Java line numbers refer to OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19` (CS = `CoordinationState.java`, CM = `CoordinationMetadata.java`, ES = `ElectionStrategy.java`, CO = `Coordinator.java`, CBS = `ClusterBootstrapService.java`), checked against the local checkout. Throughout, $V$ is an arbitrary payload type, $P$ a parameter record and $W$ a cluster; $cs_n$ abbreviates $W.\mathrm{node}(n)$, the coordination state of node $n$ in $W$, and "$m \in \mathrm{sent}$" means $W.\mathrm{sent}(m)$. Booleans are read as truth values: "$\mathrm{won}(cs)$" means `electionWon = true`, "$\neg\mathrm{won}(cs)$" means `electionWon = false`.

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

**The handler.** Each handler returns either an error (the corresponding step is then impossible) or a result. Guards are tested in the order listed; the first that applies gives the error.

- $\mathrm{setInitialState}(cs, s)$: error if $\mathrm{lac}(cs)$ is non-empty; otherwise $cs$ with $cs.\mathrm{las} := s$ (nothing else changes). Its *contract* $\mathrm{initialStateContract}(cs, s)$ is the conjunction: $\mathrm{lat}(cs) = 0$; $\mathrm{lcc}(cs)$ empty; $\mathrm{lpv}(cs) = 0$; $\mathrm{lpc}(cs)$ empty; $\neg\mathrm{won}(cs)$; $\mathrm{joinVotes}(cs)$ and $\mathrm{pubVotes}(cs)$ empty; $s.\mathrm{term} = 0$; $s.\mathrm{version} = \mathrm{lav}(cs)$; $s.\mathrm{lac}$ and $s.\mathrm{lcc}$ non-empty. *Transcription check:* CS:180-204; the contract is the eleven assertions CS:190-201.

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
2. `_hP` : $\mathrm{InitCompatible}(P)$;
3. `_hes` : $\sigma_P =$ `DEFAULT_INSTANCE`, so that $\mathrm{isElectionQuorum}_{\sigma_P}(cs, v)$ is just $\mathrm{isQuorum}(v, \mathrm{lcc}(cs)) \wedge \mathrm{isQuorum}(v, \mathrm{lac}(cs))$;
4. a cluster $W$ and `hinv` : $\mathrm{Inv}(P, W)$ — any cluster satisfying the invariant, reachable or not;
5. a node $n$, a configuration $X$, a cluster state $s$ and a coordination state $cs'$;
6. `hX` : $\mathrm{initConfs}(X)$;
7. `hcontract` : $\mathrm{initialStateContract}(cs_n, s)$, i.e. $\mathrm{lat}(cs_n) = 0$, $\mathrm{lcc}(cs_n)$ empty, $\mathrm{lpv}(cs_n) = 0$, $\mathrm{lpc}(cs_n)$ empty, $\neg\mathrm{won}(cs_n)$, $\mathrm{joinVotes}(cs_n) = \mathrm{pubVotes}(cs_n) = [\,]$, $s.\mathrm{term} = 0$, $s.\mathrm{version} = \mathrm{lav}(cs_n)$, and $s.\mathrm{lac}$, $s.\mathrm{lcc}$ non-empty;
8. `hconf` : $s.\mathrm{lcc} = X$ and $s.\mathrm{lac} = X$;
9. `h` : $\mathrm{setInitialState}(cs_n, s) = \mathrm{ok}\ cs'$, which holds exactly when $\mathrm{lac}(cs_n)$ is empty and $cs'$ is $cs_n$ with last accepted state $s$.

Items 5–9 are exactly the data and premises of the *bootstrap* step of the cluster model.

**Conclusion.** $\mathrm{Inv}(P, W.\mathrm{set}(n, cs'))$: the invariant holds in the cluster in which node $n$'s last accepted state is now $s$ — a term-0 state whose two configurations are the bootstrap configuration $X$ and whose version is $n$'s previous last accepted version — while $n$'s current term, votes, flags, $\mathrm{lpv}$ and $\mathrm{lpc}$ (still empty), every other node, and the sent set are unchanged.

## 2. What is not constrained

- `_hP` and `_hes` are genuine hypotheses (the leading underscore only silences Lean's unused-variable linter; it does not remove the hypothesis). The lemma is stated only for parameters whose bootstrap configurations are compatible and whose election strategy is the default one.
- $W$ is not required to be reachable: the lemma asserts that this step preserves $\mathrm{Inv}$ from *every* cluster satisfying $\mathrm{Inv}$ (the inductive-step form). It is exactly as strong as the claim that $\mathrm{Inv}$ is inductive for this step.
- Apart from `_hP`, $\mathrm{elig}$ and $\mathrm{initConfs}$ are arbitrary, and so is the payload type $V$.
- Node $n$ need not be eligible. Its current term and its $\mathrm{started}$ flag are unconstrained: a node may bootstrap after having handled start-joins, provided its accepted state is still of term 0 with empty configurations, it holds no votes and it has not won.
- The metadata version, cluster-manager node, cluster-UUID flags and payload of $s$ are free. That $X$ is non-empty follows from `hcontract` and `hconf` together; whether $\mathrm{initConfs}$ contains $\emptyset$ is irrelevant here.
- Not vacuous. Take $\mathrm{elig}(n) \iff n = 0$, $\mathrm{initConfs} = \{\{0\}\}$ and the default strategy (then $\mathrm{InitCompatible}(P)$ holds), and the initial cluster in which every node is $\mathrm{init}(\mathrm{dn}(n), 0, s_0)$ with $s_0$ of term 0, version 0 and empty configurations. Node 0 can then, in order: (0) bootstrap with $s_b$ (term 0, version 0, both configurations $\{0\}$); (1) handle the start-join $(\mathrm{dn}(0), 1)$, sending $j = \langle \mathrm{dn}(0), \mathrm{dn}(0), 1, 0, s_b.\mathrm{mv}\rangle$; (2) handle $j$ and win with votes $[0]$; (3) publish $s_1$ (term 1, version 1, both configurations $\{0\}$) with ghost parent $(0, 0)$; (4) accept $s_1$ and send the response $\langle 1, 1\rangle$ to itself; (5) count that response, which is a publish quorum, and send $\mathsf{commit}(\langle \mathrm{dn}(0), 1, 1\rangle)$; (6) apply that commit. By direct inspection, each cluster before one of these steps satisfies $\mathrm{Inv}$ (most conjuncts are vacuous; the others are witnessed by the single join, publication, response and commit). The hypotheses of this lemma hold for step (0).

## 3. Plain-language summary

If a cluster satisfies the invariant and a node that has no accepted configuration yet bootstraps — taking a term-0 state whose committed and accepted configurations are an allowed bootstrap configuration — the resulting cluster satisfies the invariant too, provided the bootstrap configurations are pairwise compatible and the election strategy is the default one.
