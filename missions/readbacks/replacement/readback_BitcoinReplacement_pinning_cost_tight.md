# Read-back: `BitcoinReplacement.pinning_cost_tight`

**Setting (unfolded from the preamble).** All declarations live in a namespace `BitcoinReplacement`. A *transaction* $t$ is a pair of natural numbers $(\operatorname{fee}(t), \operatorname{vsize}(t))$ together with a proof that $\operatorname{vsize}(t) > 0$; $\operatorname{fee}(t)$ may be $0$. Two transactions are equal exactly when their fees and virtual sizes agree. A *fee rate* $r$ is a pair of natural numbers $(r_{\mathrm{fee}}, r_{\mathrm{size}})$ together with a proof that $r_{\mathrm{size}} > 0$; $r_{\mathrm{fee}}$ may be $0$, and nothing identifies $(1,2)$ with $(2,4)$. For a fee rate $r$ and a natural number $v$,
$$\operatorname{getFee}_r(v) \;=\; \left\lfloor \frac{r_{\mathrm{fee}}\cdot v + (r_{\mathrm{size}} - 1)}{r_{\mathrm{size}}} \right\rfloor ,$$
computed with natural-number (rounding-down) division; since $r_{\mathrm{size}} \ge 1$ the inner subtraction $r_{\mathrm{size}}-1$ is exact, and the value equals $\lceil r_{\mathrm{fee}}\, v / r_{\mathrm{size}}\rceil$. In particular $\operatorname{getFee}_r(0) = 0$, and $\operatorname{getFee}_r(v) = 0$ for every $v$ whenever $r_{\mathrm{fee}} = 0$.

A *replacement* $R$ consists of a transaction $R.\mathrm{new}$, a multiset of transactions $R.\mathrm{evicted}$, a multiset of transactions $R.\mathrm{direct}$, and a proof that $R.\mathrm{direct} \le R.\mathrm{evicted}$ as multisets (every transaction value occurs in $R.\mathrm{direct}$ at most as many times as it occurs in $R.\mathrm{evicted}$). Either multiset may be empty, $R.\mathrm{new}$ may itself occur in $R.\mathrm{evicted}$, and no other relation between the three components is imposed. For a multiset $s$ of transactions, $\operatorname{totalFee}(s) = \sum_{u \in s} \operatorname{fee}(u)$, summed with multiplicity, so $\operatorname{totalFee}(\varnothing) = 0$.

$R$ is *valid at rate $r$* (written $\operatorname{Valid}(r,R)$) when all three of the following hold:
1. ($\operatorname{PaysMoreThanConflicts}(R)$) for every transaction value $u$ occurring in $R.\mathrm{direct}$, $\operatorname{fee}(u)\cdot\operatorname{vsize}(R.\mathrm{new}) < \operatorname{fee}(R.\mathrm{new})\cdot\operatorname{vsize}(u)$ (a strict cross-multiplied comparison in $\mathbb{N}$; vacuously true when $R.\mathrm{direct}$ is empty; nothing is required of elements of $R.\mathrm{evicted}$ that do not occur in $R.\mathrm{direct}$);
2. ($\operatorname{PaysForRBF}(r,R)$, first conjunct) $\operatorname{totalFee}(R.\mathrm{evicted}) \le \operatorname{fee}(R.\mathrm{new})$;
3. ($\operatorname{PaysForRBF}(r,R)$, second conjunct) $\operatorname{getFee}_r(\operatorname{vsize}(R.\mathrm{new})) \le \operatorname{fee}(R.\mathrm{new}) \mathbin{\dot-} \operatorname{totalFee}(R.\mathrm{evicted})$, where $\dot-$ is truncated natural-number subtraction (it returns $0$ when the subtrahend exceeds the minuend; under item 2 it coincides with ordinary subtraction).

For a transaction $t$ and a multiset $D$ of transactions, $t ::_m D$ denotes the multiset obtained from $D$ by adding one further copy of $t$.

**Statement.** For every fee rate $r$, every transaction $t$, every multiset $D$ of transactions, and every replacement $R$ such that
$$R.\mathrm{evicted} \;=\; t ::_m D$$
as an equality of multisets (so $R.\mathrm{evicted}$ is nonempty and consists exactly of one copy of $t$ together with the elements of $D$), the following two conditions are equivalent:
- **Left side:** $\operatorname{PaysForRBF}(r, R)$, i.e.
  $$\operatorname{totalFee}(R.\mathrm{evicted}) \le \operatorname{fee}(R.\mathrm{new}) \quad\text{and}\quad \operatorname{getFee}_r(\operatorname{vsize}(R.\mathrm{new})) \le \operatorname{fee}(R.\mathrm{new}) \mathbin{\dot-} \operatorname{totalFee}(R.\mathrm{evicted}),$$
  with $\dot-$ truncated natural-number subtraction;
- **Right side:**
  $$\operatorname{fee}(t) + \operatorname{totalFee}(D) + \operatorname{getFee}_r(\operatorname{vsize}(R.\mathrm{new})) \;\le\; \operatorname{fee}(R.\mathrm{new}).$$

**Edge cases and scope.** No validity hypothesis is assumed: $\operatorname{PaysMoreThanConflicts}(R)$ is neither assumed nor part of either side, and $R.\mathrm{direct}$ is not mentioned (it is constrained only by the built-in requirement $R.\mathrm{direct} \le R.\mathrm{evicted}$). $D$ may be empty. Under the hypothesis, $\operatorname{totalFee}(R.\mathrm{evicted}) = \operatorname{fee}(t) + \operatorname{totalFee}(D)$. If $r_{\mathrm{fee}} = 0$ the $\operatorname{getFee}$ term is $0$. The equivalence is a biconditional.
