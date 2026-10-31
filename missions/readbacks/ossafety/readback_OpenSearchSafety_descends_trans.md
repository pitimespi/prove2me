# Read-back: `OpenSearchSafety.descends_trans`

## Notions used

**Clusters and publications.** A *cluster* $W$ (for an arbitrary payload type $V$) consists of a coordination state $W.\mathrm{node}(n)$ for every natural number $n$ and a predicate $W.\mathrm{sent}$ on messages ("has been sent"); for an arbitrary $W$ the sent messages form an arbitrary, possibly infinite, set. Among the messages are the publish requests $\mathrm{PR}(\mathit{src}, s, pt, pv)$ (Lean `.publishRequest src s pt pv`): from node $\mathit{src} \in \mathbb{N}$, carrying a cluster state $s$ — with a term $s.\mathrm{term} \in \mathbb{N}$ and a version $s.\mathrm{version} \in \mathbb{Z}$, among other fields — and a *ghost parent key* $(pt, pv) \in \mathbb{N} \times \mathbb{Z}$. A *key* is a pair $(t, v) \in \mathbb{N} \times \mathbb{Z}$. No other message kind and no node state plays a role in this statement.

**Parent and descent.** $\mathrm{Parent}\big((t, v), (t', v')\big)$ holds iff some $\mathrm{PR}(\mathit{src}, s, t, v)$ has been sent with $(s.\mathrm{term}, s.\mathrm{version}) = (t', v')$: a publication of key $(t', v')$ whose ghost parent is $(t, v)$. Descent, Lean `Descends W t v t' v'`, written here $(t, v) \preceq (t', v')$ — the **first** key is the ancestor — is the least relation that contains $(t, v) \preceq (t, v)$ for every key (`refl`) and contains $(t, v) \preceq (t'', v'')$ whenever $(t, v) \preceq (t', v')$ and $\mathrm{Parent}\big((t', v'), (t'', v'')\big)$ (`step`, which appends a parent step at the descendant end). Equivalently, $(t, v) \preceq (t', v')$ iff there is a chain $(t, v) = k_0, k_1, \dots, k_m = (t', v')$ with $m \ge 0$ and $\mathrm{Parent}(k_i, k_{i+1})$ for each $i < m$.

## 1. Declaration

**Binders and hypotheses**, in order:

1. A type $V$ (implicit) and a cluster $W$ over $V$.
2. Natural numbers $t_1, t_2, t_3$ and integers $v_1, v_2, v_3$.
3. `h₁` : $(t_1, v_1) \preceq (t_2, v_2)$.
4. `h₂` : $(t_2, v_2) \preceq (t_3, v_3)$.

**Conclusion.**
$$(t_1, v_1) \preceq (t_3, v_3).$$
Concatenating a parent chain from $(t_1, v_1)$ to $(t_2, v_2)$ with a parent chain from $(t_2, v_2)$ to $(t_3, v_3)$ yields a parent chain from $(t_1, v_1)$ to $(t_3, v_3)$.

## 2. What is not constrained

- There are no parameters $P$, no invariant and no reachability hypothesis: $W$ is completely arbitrary (any node states, any set of sent messages, including sets in which descent has cycles or a key has several parents).
- The keys are arbitrary and may coincide; either chain may have length zero.
- The hypotheses are satisfiable (for instance with three equal keys), so the statement is not vacuous; it is a general property of the reflexive–transitive closure defining `Descends`, and holds in every cluster.

## 3. Plain-language summary

In every cluster, descent between (term, version) keys is transitive: if a key descends from a second key, which descends from a third, then the first descends from the third.
