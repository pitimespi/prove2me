# Read-back: `OpenSearchSafety.bootstrap_compatible`

## Notions used

**Sources and conventions.** Rendered from `Definitions/Def_OpenSearchCoordination.lean` (configurations, `hasQuorum`), `Definitions/Def_OpenSearchSafety.lean` (`BootstrapConfig`) and the stub `Theorems/Thm_OpenSearchSafety_bootstrap_compatible.lean`; Java line numbers refer to OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19` (CM = `CoordinationMetadata.java`, CBS = `ClusterBootstrapService.java`), checked against the local checkout. The statement uses no cluster, parameter record or coordination state.

**Nodes, configurations, quorums.** Node ids are natural numbers. A *discovery node* $d$ is a pair $(d.\mathrm{id}, d.\mathrm{cm})$ of an id and a Boolean (`isClusterManagerNode`). A *voting configuration* $c$ is a strictly increasing list of node ids, hence duplicate-free; two configurations are equal exactly when they have the same members. $\emptyset$ denotes the empty configuration `EMPTY_CONFIG`; "$c$ is empty" means its list is empty. For a configuration $c$ and any list $q$ of ids,
$$\mathrm{hasQuorum}(c, q) \iff 2\cdot\big|\{x \in c : x \in q\}\big| > |c| ,$$
so the empty configuration has no quorum, and ids of $q$ outside $c$ as well as repetitions in $q$ are irrelevant. *Transcription check:* matches `VotingConfiguration.hasQuorum` (CM:405-409).

**Bootstrap configurations.** For $k \in \mathbb{N}$, functions $\mathrm{resolve}, \mathrm{placeholder} : \mathbb{N} \to \mathbb{N}$, $\mathrm{matched} : \mathbb{N} \to \mathrm{Bool}$ and a configuration $X$, $\mathrm{BootstrapConfig}(k, \mathrm{resolve}, \mathrm{placeholder}, \mathrm{matched}, X)$ holds when
1. for every id $x$: $x \in X \iff \exists i < k,\ x = r_i$, where $r_i = \mathrm{resolve}(i)$ if $\mathrm{matched}(i)$ and $r_i = \mathrm{placeholder}(i)$ otherwise; and
2. $2 \cdot \big|\{ i < k : \mathrm{matched}(i)\}\big| > k$.

(The definition fixes the member set of $X$ only; values of the three functions at arguments $\ge k$ are irrelevant.) *Citation check:* in `ClusterBootstrapService.java`, `checkRequirements` (CBS:306-335) matches each requirement against the discovered nodes, throwing if a requirement matches several nodes or a node several requirements; `onFoundPeersUpdated` (CBS:176-215) bootstraps when the matched nodes outnumber half the requirements (CBS:211, the same count as conjunct 2) and the local node is among them (CBS:202-209, not represented); `startBootstrap` (CBS:259-273) builds the configuration from the matched nodes' ids and `"{bootstrap-placeholder}-" + requirement` for the unmatched requirements, as in conjunct 1. The best-effort bootstrap without configured requirements (`scheduleUnconfiguredBootstrap`, CBS:217-250, `startBootstrap(discoveredNodes, emptyList())`) is not described by this definition.


## 1. Declaration

**Binders and hypotheses**, in order:

1. a function $\mathrm{eligible} : \mathbb{N} \to \mathrm{Bool}$ (a free parameter, not a parameter record);
2. $k \in \mathbb{N}$ and functions $\mathrm{resolve}, \mathrm{placeholder} : \mathbb{N} \to \mathbb{N}$;
3. `hres` : for all $i, j < k$, $\mathrm{resolve}(i) = \mathrm{resolve}(j) \Rightarrow i = j$;
4. `hph` : for all $i, j < k$, $\mathrm{placeholder}(i) = \mathrm{placeholder}(j) \Rightarrow i = j$;
5. `hdis` : for all $i, j < k$, $\mathrm{placeholder}(i) \ne \mathrm{resolve}(j)$;
6. `hphe` : for all $i < k$, $\mathrm{eligible}(\mathrm{placeholder}(i)) =$ false;
7. configurations $X$, $Y$ and functions $m_X, m_Y : \mathbb{N} \to \mathrm{Bool}$;
8. `hX` : $\mathrm{BootstrapConfig}(k, \mathrm{resolve}, \mathrm{placeholder}, m_X, X)$ and `hY` : $\mathrm{BootstrapConfig}(k, \mathrm{resolve}, \mathrm{placeholder}, m_Y, Y)$;
9. lists $q_1$, $q_2$ of ids, with `hq₁` : every $x \in q_1$ has $\mathrm{eligible}(x) =$ true, and `hq₂` : every $x \in q_2$ has $\mathrm{eligible}(x) =$ true;
10. `h₁` : $\mathrm{hasQuorum}(X, q_1)$ and `h₂` : $\mathrm{hasQuorum}(Y, q_2)$.

**Conclusion.** $\exists x,\ x \in q_1 \wedge x \in q_2$.

Unfolded: the members of $X$ are $r^X_i$ for $i < k$ — $\mathrm{resolve}(i)$ if $m_X(i)$, $\mathrm{placeholder}(i)$ otherwise — and by `hres`, `hph`, `hdis` these are pairwise distinct, so $X$ has exactly $k$ members, and likewise $Y$. `h₁` says that more than $k/2$ members of $X$ occur in $q_1$; by `hq₁` and `hphe` these are all of the form $\mathrm{resolve}(i)$. The conclusion is that $q_1$ and $q_2$ share an id.

## 2. What is not constrained

- No parameter record appears. The conclusion has the shape of $\mathrm{InitCompatible}$ for the family of configurations $\{X : \exists m,\ \mathrm{BootstrapConfig}(k, \mathrm{resolve}, \mathrm{placeholder}, m, X)\}$ with $\mathrm{eligible}$ as eligibility, but the statement does not link that family to any $P.\mathrm{initConfs}$, nor $\mathrm{eligible}$ to any $P.\mathrm{elig}$; every cluster-level safety theorem keeps $\mathrm{InitCompatible}(P)$ as an assumption.
- $X$ and $Y$ share $k$, $\mathrm{resolve}$ and $\mathrm{placeholder}$: the two bootstrapping nodes have the same requirement list and resolve every matched requirement to the same node; they may differ only in which requirements they matched. In Java a requirement is matched by node name or address at each bootstrapping node (CBS:300-304), so this is an assumption (the module docstring lists "bootstrap requirements name the same node at every node").
- Resolved ids are not required to be eligible; if, for instance, no resolved id is eligible, `h₁` cannot hold and the statement is vacuous. For $k = 0$, conjunct 2 of $\mathrm{BootstrapConfig}$ ($0 > 0$) fails, so the statement is vacuous.
- Conjunct 2 of $\mathrm{BootstrapConfig}$ is not needed for the conclusion: given `hq₁`, `hphe` and injectivity, `h₁` already forces more than $k/2$ indices $i < k$ with $m_X(i)$ and $\mathrm{resolve}(i) \in q_1$; two such sets of more than $k/2$ ids among the $k$ ids $\mathrm{resolve}(0), \dots, \mathrm{resolve}(k-1)$ must meet.
- Not vacuous: $k = 1$, $\mathrm{resolve}(0) = 1$, $\mathrm{placeholder}(0) = 2$, $\mathrm{eligible}(x) \iff x = 1$, $m_X = m_Y = $ true, $X = Y = \{1\}$, $q_1 = q_2 = [1]$.
- Only the requirements-based bootstrap path is described; the best-effort bootstrap without configured requirements (CBS:217-250) is outside $\mathrm{BootstrapConfig}$.

## 3. Plain-language summary

Two voting configurations built from the same bootstrap requirements resolved to the same nodes — differing only in which requirements were matched, with placeholder ids distinct, distinct from real ids and not eligible — have intersecting quorums when quorums are made of eligible nodes. This is the compatibility property a parameter record needs for such configurations, but the theorem does not itself state $\mathrm{InitCompatible}$ for any parameter record.
