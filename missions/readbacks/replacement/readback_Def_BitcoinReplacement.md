# Read-back: `Def_BitcoinReplacement.lean` (preamble definitions)

The file imports Mathlib and places every declaration below in a namespace `BitcoinReplacement`. Throughout, $\mathbb{N}$ denotes the natural numbers $\{0,1,2,\dots\}$; subtraction in $\mathbb{N}$ truncates at $0$ ($a \mathbin{\dot-} b = 0$ when $b > a$) and division in $\mathbb{N}$ rounds down. Multisets, the operation $t ::_m D$ (add one copy of $t$ to $D$) and the sub-multiset order $\le$ on multisets are the standard Mathlib notions. One paragraph follows per definition, in file order.

**1. `Tx` (transaction).** A structure with two data fields, $\operatorname{fee} \in \mathbb{N}$ and $\operatorname{vsize} \in \mathbb{N}$, and one proof field asserting $0 < \operatorname{vsize}$. Thus a transaction is exactly a pair $(\operatorname{fee}, \operatorname{vsize})$ of natural numbers with $\operatorname{vsize} \ge 1$; the fee may be $0$. Equality of transactions is decidable and two transactions are equal exactly when their fee and vsize agree (the proof field carries no information). No identifier, inputs, outputs or any other attribute exists in this notion.

**2. `FeeRate` (fee rate).** A structure with two data fields, $\mathrm{fee} \in \mathbb{N}$ and $\mathrm{size} \in \mathbb{N}$, and a proof field asserting $0 < \mathrm{size}$. Thus a fee rate is a pair $(\mathrm{fee}, \mathrm{size})$ of natural numbers with $\mathrm{size} \ge 1$; the numerator may be $0$. Fee rates are *not* identified up to proportion: $(1,2)$ and $(2,4)$ are distinct values of this type.

**3. `FeeRate.perKvB`.** A function sending a natural number $k$ to the fee rate $(k, 1000)$, i.e. numerator $k$ and denominator $1000$.

**4. `DEFAULT_INCREMENTAL_RELAY_FEE`.** The natural-number constant $100$.

**5. `defaultIncrementalRelayFee`.** The fee rate $\operatorname{perKvB}(100)$, i.e. the pair $(100, 1000)$.

**6. `MAX_REPLACEMENT_CANDIDATES`.** The natural-number constant $100$. It is not referenced by any other definition in this file.

**7. `FeeRate.getFee`.** For a fee rate $r = (r_{\mathrm{fee}}, r_{\mathrm{size}})$ and a natural number $v$,
$$\operatorname{getFee}_r(v) \;=\; \left\lfloor \frac{r_{\mathrm{fee}}\cdot v + (r_{\mathrm{size}} - 1)}{r_{\mathrm{size}}} \right\rfloor ,$$
with natural-number (rounding-down) division. Because $r_{\mathrm{size}} \ge 1$, the inner subtraction $r_{\mathrm{size}} - 1$ never truncates, and the whole expression equals the ceiling $\lceil r_{\mathrm{fee}}\, v / r_{\mathrm{size}} \rceil$. Edge cases: $\operatorname{getFee}_r(0) = 0$ for every $r$; $\operatorname{getFee}_r(v) = 0$ for every $v$ when $r_{\mathrm{fee}} = 0$; when $r_{\mathrm{fee}} \ge 1$ and $v \ge 1$ the value is at least $1$; when $r_{\mathrm{size}} = 1$ it is exactly $r_{\mathrm{fee}}\cdot v$.

**8. `Tx.feeRate`.** For a transaction $t$, the fee rate $\operatorname{feeRate}(t) = (\operatorname{fee}(t), \operatorname{vsize}(t))$, with the positivity proof inherited from $t$. No reduction of the fraction is performed.

**9. `FeeRate.lt`.** For fee rates $a = (a_{\mathrm{fee}}, a_{\mathrm{size}})$ and $b = (b_{\mathrm{fee}}, b_{\mathrm{size}})$, the proposition
$$\operatorname{lt}(a,b) \;:\Longleftrightarrow\; a_{\mathrm{fee}}\cdot b_{\mathrm{size}} \;<\; b_{\mathrm{fee}}\cdot a_{\mathrm{size}},$$
a strict inequality of natural numbers obtained by cross-multiplication, with no rounding. Edge cases: $\operatorname{lt}(a,a)$ is false; if $a_{\mathrm{fee}} = 0$ then $\operatorname{lt}(a,b)$ holds exactly when $b_{\mathrm{fee}} > 0$; if $b_{\mathrm{fee}} = 0$ then $\operatorname{lt}(a,b)$ is false.

**10. `FeeRate.le`.** For fee rates $a$ and $b$ as above, the proposition $\operatorname{le}(a,b) :\Longleftrightarrow a_{\mathrm{fee}}\cdot b_{\mathrm{size}} \le b_{\mathrm{fee}}\cdot a_{\mathrm{size}}$, the non-strict cross-multiplied comparison. It is not referenced by any other definition in this file.

**11. `Tx.feeRateQ`.** For a transaction $t$, the rational number $\operatorname{feeRateQ}(t) = \operatorname{fee}(t)/\operatorname{vsize}(t) \in \mathbb{Q}$, where both naturals are cast into $\mathbb{Q}$ and the division is exact rational division. Since $\operatorname{vsize}(t) > 0$, the division-by-zero convention of $\mathbb{Q}$ is never invoked; $\operatorname{feeRateQ}(t) = 0$ exactly when $\operatorname{fee}(t) = 0$.

**12. `Replacement`.** A structure with three data fields and one proof field: a transaction $\mathrm{new}$; a multiset of transactions $\mathrm{evicted}$; a multiset of transactions $\mathrm{direct}$; and a proof that $\mathrm{direct} \le \mathrm{evicted}$ in the sub-multiset order (every transaction value occurs in $\mathrm{direct}$ at most as many times as in $\mathrm{evicted}$). Nothing else is required: $\mathrm{evicted}$ and $\mathrm{direct}$ may both be empty, $\mathrm{direct}$ may equal $\mathrm{evicted}$, $\mathrm{new}$ may itself occur in $\mathrm{evicted}$ or $\mathrm{direct}$, and multiple copies of equal $(\operatorname{fee}, \operatorname{vsize})$ data are kept distinct by multiplicity only. There is no notion of mempool, conflict, inputs or descendants in the definition; the names of the fields are the only link to such notions.

**13. `totalFee`.** For a multiset $s$ of transactions, $\operatorname{totalFee}(s) = \sum_{u \in s} \operatorname{fee}(u) \in \mathbb{N}$, the sum of the fees counted with multiplicity. For the empty multiset the value is $0$.

**14. `totalVsize`.** For a multiset $s$ of transactions, $\operatorname{totalVsize}(s) = \sum_{u \in s} \operatorname{vsize}(u) \in \mathbb{N}$, counted with multiplicity; $0$ for the empty multiset. It is not referenced by any other definition in this file.

**15. `PaysMoreThanConflicts`.** For a replacement $R$, the proposition
$$\forall\, u \text{ occurring in } R.\mathrm{direct}:\quad \operatorname{lt}(\operatorname{feeRate}(u), \operatorname{feeRate}(R.\mathrm{new})),\ \text{i.e.}\ \operatorname{fee}(u)\cdot\operatorname{vsize}(R.\mathrm{new}) < \operatorname{fee}(R.\mathrm{new})\cdot\operatorname{vsize}(u).$$
The quantification ranges over the elements of $R.\mathrm{direct}$ only (not $R.\mathrm{evicted}$), and multiplicity is irrelevant to it. It is vacuously true when $R.\mathrm{direct}$ is empty. If $\operatorname{fee}(R.\mathrm{new}) = 0$ it holds only when $R.\mathrm{direct}$ is empty.

**16. `PaysForRBF`.** For a fee rate $r$ and a replacement $R$, the conjunction of two natural-number inequalities:
$$\operatorname{totalFee}(R.\mathrm{evicted}) \;\le\; \operatorname{fee}(R.\mathrm{new})
\qquad\text{and}\qquad
\operatorname{getFee}_r(\operatorname{vsize}(R.\mathrm{new})) \;\le\; \operatorname{fee}(R.\mathrm{new}) \mathbin{\dot-} \operatorname{totalFee}(R.\mathrm{evicted}),$$
where $\dot-$ is truncated subtraction in $\mathbb{N}$. Under the first conjunct the subtraction in the second is an ordinary difference; taken on its own, the second conjunct would be satisfied with right-hand side $0$ whenever $\operatorname{totalFee}(R.\mathrm{evicted}) \ge \operatorname{fee}(R.\mathrm{new})$ and $\operatorname{getFee}_r(\operatorname{vsize}(R.\mathrm{new})) = 0$. $R.\mathrm{direct}$ does not appear. Edge cases: if $R.\mathrm{evicted}$ is empty the condition is $\operatorname{getFee}_r(\operatorname{vsize}(R.\mathrm{new})) \le \operatorname{fee}(R.\mathrm{new})$; if $r_{\mathrm{fee}} = 0$ it is $\operatorname{totalFee}(R.\mathrm{evicted}) \le \operatorname{fee}(R.\mathrm{new})$.

**17. `Valid`.** For a fee rate $r$ and a replacement $R$, the conjunction $\operatorname{PaysMoreThanConflicts}(R) \wedge \operatorname{PaysForRBF}(r, R)$, i.e. all three inequalities of items 15 and 16 together.

**18. `IsChain`.** For a fee rate $r$, a transaction $t$ and a list of replacements, a proposition defined by recursion on the list: for the empty list it is *true* (for any $t$ and $r$); for a list whose first element is $R$ and whose remainder is $Rs$, it is
$$\operatorname{Valid}(r, R)\;\wedge\; t \in R.\mathrm{evicted} \;\wedge\; \operatorname{IsChain}(r, R.\mathrm{new}, Rs).$$
Unfolded for $[R_1, \dots, R_n]$ with $t_0 = t$ and $t_i = R_i.\mathrm{new}$: for each $1 \le i \le n$, $R_i$ is valid at rate $r$ and the transaction value $t_{i-1}$ occurs (with any multiplicity $\ge 1$) in $R_i.\mathrm{evicted}$. Membership is by value: any element with the same fee and vsize as $t_{i-1}$ counts. It is not required that $t_{i-1}$ occur in $R_i.\mathrm{direct}$, that $R_i.\mathrm{evicted}$ contain nothing besides $t_{i-1}$, that the $t_i$ be distinct, or that $t_i \ne t_{i-1}$.

**19. `chainEnd`.** For a transaction $t_0$ and a list of replacements, a left fold whose step function discards the accumulator and returns $R.\mathrm{new}$ for the current element $R$. Hence $\operatorname{chainEnd}(t_0, []) = t_0$ and $\operatorname{chainEnd}(t_0, [R_1,\dots,R_n]) = R_n.\mathrm{new}$ for $n \ge 1$; the result depends only on the last element of the list, and on $t_0$ only when the list is empty. No chain hypothesis is involved in the definition.

**20. `chainVsizes`.** For a list of replacements $[R_1,\dots,R_n]$, the list of natural numbers $[\operatorname{vsize}(R_1.\mathrm{new}), \dots, \operatorname{vsize}(R_n.\mathrm{new})]$, in order; the empty list when $n = 0$. The vsize of any starting transaction $t_0$ is not included.
