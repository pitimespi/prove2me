# Read-back: `OpenSearchSafety.inv_won_of_electionWon`

## Notions used

**Model and notation.** Node ids are natural numbers. The parameters $P$ consist of an eligibility function $P.\mathrm{eligible} : \mathbb{N} \to \mathrm{Bool}$ (write $E(x)$ for $P.\mathrm{eligible}(x) = \mathrm{true}$, "$x$ is cluster-manager-eligible"), a predicate $P.\mathrm{initConfs}$ on voting configurations (the *bootstrap configurations*; it may be empty or have any number of elements), and an election strategy $P.\mathrm{strategy}$. $P.\mathrm{dn}(n)$ is the discovery node with id $n$ and cluster-manager flag $P.\mathrm{eligible}(n)$.

A *voting configuration* $c$ is a strictly increasing list $c.\mathrm{nodeIds}$ of node ids, so two configurations are equal exactly when they contain the same ids; $\mathrm{EMPTY}$ is the empty one. For a list $q$ of node ids, "$q$ is a quorum of $c$", Lean `c.hasQuorum q = true`, means
$$2\cdot\big|\{x \in c.\mathrm{nodeIds} : x \in q\}\big| > |c.\mathrm{nodeIds}|,$$
i.e. strictly more than half of the members of $c$ occur in $q$; the order of $q$, repetitions in $q$ and members of $q$ outside $c$ are irrelevant, and $\mathrm{EMPTY}$ has no quorum at all.

A *cluster state* $s$ has a term $s.\mathrm{term} \in \mathbb{N}$, a version $s.\mathrm{version} \in \mathbb{Z}$, a metadata version, a last committed configuration $s.\mathrm{lcc}$, a last accepted configuration $s.\mathrm{lac}$, an optional cluster-manager id, two Boolean cluster-UUID flags, and a payload of the arbitrary type $V$. A *key* is a pair $(t, v) \in \mathbb{N} \times \mathbb{Z}$; the key of $s$ is $(s.\mathrm{term}, s.\mathrm{version})$.

A *cluster* $W$ consists of a coordination state $W.\mathrm{node}(n)$ for **every** natural number $n$ and a predicate $W.\mathrm{sent}$ on messages ("has been sent"); for an arbitrary $W$ the sent messages form an arbitrary, possibly infinite, set. Messages are of four kinds:

- $\mathrm{join}(j)$, where a join $j$ consists of a source discovery node $j.\mathrm{src}$ and a target discovery node $j.\mathrm{tgt}$ (each an id and a flag), a term $j.\mathrm{term} \in \mathbb{N}$, a last accepted term $j.\mathrm{lat} \in \mathbb{N}$ and a last accepted version $j.\mathrm{lav} \in \mathbb{Z}$;
- $\mathrm{PR}(\mathit{src}, s, pt, pv)$ (Lean `.publishRequest src s pt pv`), a publish request from node $\mathit{src}$ carrying the cluster state $s$ and the *ghost parent key* $(pt, pv) \in \mathbb{N} \times \mathbb{Z}$;
- $\mathrm{RESP}(a, d, (t, v))$, a publish response from node $a$ to node $d$ for the key $(t, v)$;
- $\mathrm{AC}(\sigma, t, v)$, an apply-commit request with source discovery node $\sigma$ and key $(t, v)$.

A *publication* is a sent message $\mathrm{PR}(\mathit{src}, s, pt, pv)$; its key is the key of $s$ and its parent is $(pt, pv)$. In the model's steps, a node publishes $\mathrm{PR}(n, s, \mathrm{lat}(n), \mathrm{lav}(n))$, so the ghost parent is the publisher's accepted key at publication time; but the statements below are about arbitrary clusters satisfying the invariant, where only the invariant constrains $W.\mathrm{sent}$.

For a node $n$, read off its coordination state $W.\mathrm{node}(n)$: $\mathrm{ln}(n)$ its local discovery node; $T(n)$ its current term; $\mathrm{lat}(n)$, $\mathrm{lav}(n)$, $\mathrm{lcc}(n)$, $\mathrm{lac}(n)$ the term, version, last committed and last accepted configuration of its last accepted state; $\mathrm{won}(n)$ its election-won flag; $\mathrm{started}(n)$ its started-join-since-last-reboot flag; $\mathrm{lpv}(n)$ and $\mathrm{lpc}(n)$ its last published version and configuration; $\mathrm{JV}(n)$ and $\mathrm{PV}(n)$ the node-id lists of its join votes and publish votes.

**Committed keys.** $\mathrm{Committed}(t, v)$ (Lean `Committed W t v`) holds iff some message $\mathrm{AC}(\sigma, t, v)$ has been sent, for some source discovery node $\sigma$. The definition alone does not require $(t, v)$ to be the key of a publication.

**Parent and descent.** $\mathrm{Parent}\big((t, v), (t', v')\big)$ holds iff some publication $\mathrm{PR}(\mathit{src}, s, t, v)$ has been sent with $(s.\mathrm{term}, s.\mathrm{version}) = (t', v')$: a publication of key $(t', v')$ whose ghost parent is $(t, v)$. Descent, Lean `Descends W t v t' v'`, written here $(t, v) \preceq (t', v')$ and read "$(t', v')$ descends from $(t, v)$" — the **first** key is the ancestor — is the least relation that is reflexive on every key and closed under appending a $\mathrm{Parent}$ step: $(t, v) \preceq (t', v')$ iff there is a chain $(t, v) = k_0, k_1, \dots, k_m = (t', v')$ with $m \ge 0$ and $\mathrm{Parent}(k_i, k_{i+1})$ for each $i < m$. It is reflexive on **every** key, published or not; a key that is not the key of any publication has no ancestor but itself. "Proper" descent means $\preceq$ between two different keys. For a publication $\mathrm{PR}(\mathit{src}, s, pt, pv)$ write $\mathrm{key}(s) = (s.\mathrm{term}, s.\mathrm{version})$.

**Auxiliary relations** (over $P$ and $W.\mathrm{sent}$):

- $\mathrm{KeyLE}(t, v;\ t', v')$: $t < t' \vee (t = t' \wedge v \le v')$ — the lexicographic order on keys.
- $\mathrm{Below}(lt, lv;\ bt, bv)$: $lt < bt \vee \big(lt = bt \wedge (bt = 0 \vee lv \le bv)\big)$ — lexicographic, except that versions are not compared when both terms are $0$.
- $\mathrm{Realizes}(t, v, x, y)$, for configurations $x$ (in the role of a last committed configuration) and $y$ (last accepted): either (i) $t = 0$, $x = y$ and $P.\mathrm{initConfs}(x)$, with $v$ unconstrained; or (ii) some publication $\mathrm{PR}(\mathit{src}, s, pt, pv)$ has key $(t, v)$, $y = s.\mathrm{lac}$, and either $x = s.\mathrm{lcc}$ or ($x = s.\mathrm{lac}$ and $\mathrm{Committed}(t, v)$).
- $\mathrm{JoinVoters}(L, t, J)$, for a list $J$ of node ids: every $x \in J$ has $E(x)$ and there is a sent $\mathrm{join}(j)$ with $j.\mathrm{src}.\mathrm{id} = x$, $j.\mathrm{tgt}.\mathrm{id} = L$ and $j.\mathrm{term} = t$.
- $\mathrm{BaseVoters}(L, t, bt, bv, J)$: the same, and moreover that join satisfies $\mathrm{Below}(j.\mathrm{lat}, j.\mathrm{lav};\ bt, bv)$.
- $\mathrm{RespVoters}(t, v, A)$: every $x \in A$ has $E(x)$ and $\mathrm{RESP}(x, d, (t, v))$ has been sent for some node $d$ (any destination).
- $\mathrm{ElectionRecord}(L, t, bt, bv, x, y, J)$: $bt < t$, $\mathrm{Realizes}(bt, bv, x, y)$, $\mathrm{BaseVoters}(L, t, bt, bv, J)$, $J$ is a quorum of $x$ and $J$ is a quorum of $y$. The key $(bt, bv)$ is the *base*. (Since $J$ is a quorum of $x$, $x$ and $J$ are non-empty; nothing requires $L$ to have won or published, nor the base to be published.)
- $\mathrm{Won}(b, t)$: $E(b)$, and either ($\mathrm{won}(b)$ and $T(b) = t$) or some publication $\mathrm{PR}(b, s, pt, pv)$ from $b$ has $s.\mathrm{term} = t$.

The voter lists may be empty (the voter conditions then hold vacuously) and may contain repetitions.

**The invariant $\mathrm{Inv}(P, W)$** is the conjunction of the following 30 fields (node variables range over all of $\mathbb{N}$; "sent" means in $W.\mathrm{sent}$; $\preceq$ is descent as above).

*Every node $n$:*

1. `localNode_eq`: $\mathrm{ln}(n) = P.\mathrm{dn}(n)$.
2. `idle_of_not_won`: $\neg\mathrm{won}(n) \Rightarrow \mathrm{lpv}(n) = 0 \wedge \mathrm{PV}(n) = [\,]$.
3. `won_started`: $\mathrm{won}(n) \Rightarrow \mathrm{started}(n)$.
4. `votes_started`: $\mathrm{JV}(n) \neq [\,] \Rightarrow \mathrm{started}(n)$.
5. `started_term_pos`: $\mathrm{started}(n) \Rightarrow T(n) \ge 1$.
6. `won_quorum`: $\mathrm{won}(n) \Rightarrow \mathrm{JV}(n)$ is a quorum of $\mathrm{lcc}(n)$ and of $\mathrm{lac}(n)$.
7. `not_won_no_quorum`: $\neg\mathrm{won}(n) \Rightarrow \neg\big(\mathrm{JV}(n)$ is a quorum of $\mathrm{lcc}(n)$ and of $\mathrm{lac}(n)\big)$.
8. `joinVotes_sent`: every $m \in \mathrm{JV}(n)$ has $E(m)$, and some sent $\mathrm{join}(j)$ has $j.\mathrm{src}.\mathrm{id} = m$, $j.\mathrm{tgt}.\mathrm{id} = n$, $j.\mathrm{term} = T(n)$ and $\mathrm{Below}(j.\mathrm{lat}, j.\mathrm{lav};\ \mathrm{lat}(n), \mathrm{lav}(n))$.
9. `publishVotes_sent`: every $m \in \mathrm{PV}(n)$ has $E(m)$, and $\mathrm{RESP}(m, n, (T(n), \mathrm{lpv}(n)))$ has been sent.

*Every eligible node $n$ ($E(n)$):*

10. `term_le`: $\mathrm{lat}(n) \le T(n)$.
11. `accepted_realizes`: $\big(\mathrm{lat}(n) = 0 \wedge \mathrm{lcc}(n) = \mathrm{lac}(n) = \mathrm{EMPTY}\big)$ or $\mathrm{Realizes}(\mathrm{lat}(n), \mathrm{lav}(n), \mathrm{lcc}(n), \mathrm{lac}(n))$.

*Joins and publish responses:*

12. `join_wf`: every sent $\mathrm{join}(j)$ has $j.\mathrm{src} = P.\mathrm{dn}(j.\mathrm{src}.\mathrm{id})$ and $E(j.\mathrm{tgt}.\mathrm{id})$.
13. `join_term_le`: every sent $\mathrm{join}(j)$ with $E(j.\mathrm{src}.\mathrm{id})$ has $j.\mathrm{term} \le T(j.\mathrm{src}.\mathrm{id})$.
14. `join_unique`: two sent joins with the same source id, that source eligible, and the same term are equal (all five fields, so in particular the same target).
15. `join_after_response`: for a sent $\mathrm{join}(j)$ and a sent $\mathrm{RESP}(a, d, (t, v))$ with $j.\mathrm{src}.\mathrm{id} = a$, $E(a)$ and $t < j.\mathrm{term}$: $\mathrm{KeyLE}(t, v;\ j.\mathrm{lat}, j.\mathrm{lav})$.
16. `response_le`: for a sent $\mathrm{RESP}(a, d, (t, v))$ with $E(a)$: $t \le T(a)$ and $\mathrm{KeyLE}(t, v;\ \mathrm{lat}(a), \mathrm{lav}(a))$.
17. `response_published`: for every sent $\mathrm{RESP}(a, d, (t, v))$ there is a sent publication $\mathrm{PR}(d, s, pt, pv)$ from $d$ with key $(t, v)$.

*Publications* — for every sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$:

18. `pub_wf`: $E(\mathit{src})$, $s.\mathrm{term} \ge 1$, $pt \le s.\mathrm{term}$, $pv < s.\mathrm{version}$, and $pt = 0 \Rightarrow P.\mathrm{initConfs}(s.\mathrm{lcc})$.
19. `pub_parent`: if $pt \ge 1$, there is a sent $\mathrm{PR}(\mathit{src}', s', pt', pv')$ with key $(pt, pv)$ such that (a) $s.\mathrm{lcc} = s'.\mathrm{lcc}$, or ($s.\mathrm{lcc} = s'.\mathrm{lac}$ and $\mathrm{Committed}(pt, pv)$); and (b) $s.\mathrm{lac} \neq s'.\mathrm{lac} \Rightarrow s.\mathrm{lcc} = s'.\mathrm{lac}$.
20. `pub_unique`: any two sent publications with the same key are the same message (same source, same cluster state in all fields, same parent).
21. `pub_rooted`: $(0, v_0) \preceq \mathrm{key}(s)$ for some $v_0 \in \mathbb{Z}$.
22. `pub_same_term`: for every sent $\mathrm{PR}(\mathit{src}', s', pt', pv')$ with $s'.\mathrm{term} = s.\mathrm{term}$: $\mathrm{key}(s) \preceq \mathrm{key}(s')$ or $\mathrm{key}(s') \preceq \mathrm{key}(s)$.
23. `pub_voters`: some list $J$ with $\mathrm{JoinVoters}(\mathit{src}, s.\mathrm{term}, J)$ is a quorum of $s.\mathrm{lcc}$ and of $s.\mathrm{lac}$.
24. `pub_election`: if $pt < s.\mathrm{term}$, then $\mathrm{ElectionRecord}(\mathit{src}, s.\mathrm{term}, pt, pv, s.\mathrm{lcc}, y, J)$ for some configuration $y$ and list $J$.

*Commits:*

25. `commit_quorum`: for every sent $\mathrm{AC}(\sigma, t, v)$ there are a sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$ with key $(t, v)$ and a list $A$ with $\mathrm{RespVoters}(t, v, A)$, $A$ a quorum of $s.\mathrm{lac}$, and either $A$ a quorum of $s.\mathrm{lcc}$, or ($\mathrm{Committed}(pt, pv)$ and some sent publication of key $(pt, pv)$ has last accepted configuration $s.\mathrm{lac}$).

*Leaders:*

26. `won_unique`: $\mathrm{Won}(a, t) \wedge \mathrm{Won}(b, t) \Rightarrow a = b$.
27. `pub_source_term`: for every sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$: $s.\mathrm{term} < T(\mathit{src})$, or $s.\mathrm{term} = T(\mathit{src})$ and ($\mathrm{won}(\mathit{src})$ or $\neg\mathrm{started}(\mathit{src})$).
28. `leader_pubs`: if $\mathrm{won}(n)$, every sent $\mathrm{PR}(\mathit{src}, s, pt, pv)$ with $s.\mathrm{term} = T(n)$ (any source) has $s.\mathrm{version} \le \mathrm{lpv}(n)$, $\mathrm{key}(s) \preceq (T(n), \mathrm{lpv}(n))$, and $\mathrm{JV}(n)$ a quorum of $s.\mathrm{lcc}$ and of $s.\mathrm{lac}$.
29. `leader_inflight`: if $\mathrm{won}(n)$ and $\mathrm{lpv}(n) \neq \mathrm{lav}(n)$, then for some state $s$: $\mathrm{PR}(n, s, \mathrm{lat}(n), \mathrm{lav}(n))$ is sent, $s.\mathrm{term} = T(n)$, $s.\mathrm{version} = \mathrm{lpv}(n)$, $\mathrm{lpc}(n) = s.\mathrm{lac}$, and either $\mathrm{lcc}(n) = s.\mathrm{lcc}$, or ($\mathrm{lcc}(n) = s.\mathrm{lac}$, $\mathrm{Committed}(\mathrm{lat}(n), \mathrm{lav}(n))$ and $\mathrm{lac}(n) = s.\mathrm{lac}$).
30. `leader_settled`: if $\mathrm{won}(n)$ and $\mathrm{lpv}(n) = \mathrm{lav}(n)$, then either ($\mathrm{lat}(n) = T(n)$ and $\mathrm{lpc}(n) = \mathrm{lac}(n)$), or ($\mathrm{lat}(n) < T(n)$ and no sent publication has term $T(n)$).

## 1. Declaration

**Binders and hypotheses**, in order:

1. A type $V$ (implicit), parameters $P$, a cluster $W$ over $V$, and `hinv` : $\mathrm{Inv}(P, W)$.
2. A node id $n$ and `h` : $\mathrm{won}(n) = \mathrm{true}$.

**Conclusion.** $\mathrm{Won}(n, T(n))$, which unfolds to
$$E(n) \;\wedge\; \Big( \big(\mathrm{won}(n) \wedge T(n) = T(n)\big) \;\vee\; \exists\, s, pt, pv,\ \mathrm{PR}(n, s, pt, pv) \text{ has been sent} \wedge s.\mathrm{term} = T(n) \Big).$$
Given `h`, the first alternative of the disjunction holds trivially, so the only content of the conclusion is $E(n)$ — the same conclusion as `inv_eligible_of_won`.

## 2. What is not constrained

- The statement does not assert that $n$ has published in its current term; the publication alternative is never needed.
- Nothing is said about other nodes (uniqueness of the winner of a term is field 26 of the hypothesis, not the conclusion).

*The hypothesis $\mathrm{Inv}(P, W)$.* The statement is about every cluster $W$ satisfying the 30 fields, for arbitrary parameters $P$ (any eligibility function, any bootstrap-configuration predicate, any election strategy) and any payload type $V$. Reachability is not assumed, and $P.\mathrm{InitCompatible}$ is not assumed. The hypothesis is satisfiable, so the statement is not vacuous on that account: every cluster in which no message has been sent and every node $n$ is in the state $\mathrm{init}(P.\mathrm{dn}(n), 0, s_n)$ for some state $s_n$ of term $0$ with empty configurations (the model's `Initial` clusters) satisfies all 30 fields — fields 1, 2, 10 and 11 by direct check, field 7 because $\mathrm{EMPTY}$ has no quorum, the rest vacuously. On such clusters the conclusion is trivial. That clusters with publications and commits satisfy the invariant is the subject of other stubs (`reachable_inv`, which assumes `P.InitCompatible` and the default election strategy, and `commit_reachable`), not of this statement. Neither the statement nor $\mathrm{Inv}$ mentions $P.\mathrm{strategy}$.

## 3. Plain-language summary

In any cluster satisfying the invariant, a node with its election-won flag set satisfies `Won` for its current term. Its only non-trivial part is that the node is eligible.
