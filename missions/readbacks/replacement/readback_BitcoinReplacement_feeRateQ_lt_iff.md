# Read-back: `BitcoinReplacement.feeRateQ_lt_iff`

**Setting (unfolded from the preamble).** All declarations live in a namespace `BitcoinReplacement`. A *transaction* $t$ is a pair of natural numbers $(\operatorname{fee}(t), \operatorname{vsize}(t))$ together with a proof that $\operatorname{vsize}(t) > 0$; $\operatorname{fee}(t)$ may be $0$. A *fee rate* is a pair of natural numbers $(\mathrm{fee}, \mathrm{size})$ with a proof that $\mathrm{size} > 0$. The fee rate attached to a transaction $t$, $\operatorname{feeRate}(t)$, is the pair $(\operatorname{fee}(t), \operatorname{vsize}(t))$. For fee rates $a = (a_{\mathrm{fee}}, a_{\mathrm{size}})$ and $b = (b_{\mathrm{fee}}, b_{\mathrm{size}})$, the relation $\operatorname{lt}(a, b)$ is defined as the natural-number inequality $a_{\mathrm{fee}}\cdot b_{\mathrm{size}} < b_{\mathrm{fee}}\cdot a_{\mathrm{size}}$. For a transaction $u$, $\operatorname{feeRateQ}(u) = \operatorname{fee}(u)/\operatorname{vsize}(u) \in \mathbb{Q}$ is the exact rational quotient (well defined since $\operatorname{vsize}(u) > 0$).

**Statement.** For every pair of transactions $a$ and $b$ (no further hypotheses), the following are equivalent:
$$\frac{\operatorname{fee}(a)}{\operatorname{vsize}(a)} \;<\; \frac{\operatorname{fee}(b)}{\operatorname{vsize}(b)} \quad\text{in } \mathbb{Q}
\qquad\Longleftrightarrow\qquad
\operatorname{fee}(a)\cdot\operatorname{vsize}(b) \;<\; \operatorname{fee}(b)\cdot\operatorname{vsize}(a) \quad\text{in } \mathbb{N}.$$
The left side is the strict order on rational numbers; the right side is $\operatorname{lt}(\operatorname{feeRate}(a), \operatorname{feeRate}(b))$, a strict cross-multiplied comparison of natural numbers with no rounding.

**Edge cases.** Both sides are comparisons of a transaction with another arbitrary transaction, including $a = b$ (both sides then false) and the case $\operatorname{fee}(a) = 0$ (left side holds iff $\operatorname{fee}(b) > 0$, and likewise on the right since $\operatorname{vsize}(a) > 0$). No fee rate parameter $r$ and no replacement appears in this statement.
