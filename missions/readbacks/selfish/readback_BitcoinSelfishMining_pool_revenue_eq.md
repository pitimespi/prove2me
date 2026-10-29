# Read-back: `BitcoinSelfishMining.pool_revenue_eq`

Let $\alpha,\gamma$ be real numbers with $0<\alpha$ and $\alpha<\tfrac12$ (named, usable hypotheses) and **no hypothesis on $\gamma$**. Then
$$
r^{\mathrm{pool}}_{\alpha,\gamma} \;=\; \pi_\alpha(\mathrm{tie})\cdot\big(\alpha\cdot 2 + \gamma(1-\alpha)\cdot 1\big) \;+\; \pi_\alpha(\mathrm{lead}_1)\cdot\big((1-\alpha)\cdot 2\big) \;+\; \Big(\sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_{n+2})\Big)\cdot\big((1-\alpha)\cdot 1\big).
$$

**Left-hand side.** $r^{\mathrm{pool}}_{\alpha,\gamma}$ is the custom `poolRevenue` $\alpha\,\gamma$, the custom `stateSum` of $s\mapsto\pi_\alpha(s)\,g^{\mathrm{pool}}_{\alpha,\gamma}(s)$:
$$
r^{\mathrm{pool}}_{\alpha,\gamma} = \pi_\alpha(\mathrm{zero})\,g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{zero}) + \pi_\alpha(\mathrm{tie})\,g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{tie}) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_n),
$$
with $g^{\mathrm{pool}}_{\alpha,\gamma}(s)=\sum_o p_{\alpha,\gamma}(o)\cdot\mathrm{poolGain}(s,o)$, where $p_{\alpha,\gamma}(\mathrm{pool})=\alpha$, $p_{\alpha,\gamma}(\mathrm{honestOnPool})=(1-\alpha)\gamma$, $p_{\alpha,\gamma}(\mathrm{honestOnOthers})=(1-\alpha)(1-\gamma)$, and $\mathrm{poolGain}$: $(\mathrm{tie},\mathrm{pool})\mapsto 2$, $(\mathrm{tie},\mathrm{honestOnPool})\mapsto 1$, $(\mathrm{tie},\mathrm{honestOnOthers})\mapsto 0$, $(\mathrm{lead}_1,\mathrm{pool})\mapsto 0$, $(\mathrm{lead}_1,\text{either honest})\mapsto 2$, $(\mathrm{lead}_{m+2},\mathrm{pool})\mapsto 0$, $(\mathrm{lead}_{m+2},\text{either honest})\mapsto 1$, and $0$ otherwise (all of $\mathrm{zero}$ and all of $\mathrm{lead}_0$). Hence
$$
g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{zero}) = 0,\quad
g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{tie}) = 2\alpha + (1-\alpha)\gamma,\quad
g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_0) = 0,\quad
g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_1) = 2(1-\alpha)\gamma + 2(1-\alpha)(1-\gamma),\quad
g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_{m+2}) = (1-\alpha)\gamma + (1-\alpha)(1-\gamma).
$$
So the left-hand side equals $\pi_\alpha(\mathrm{tie})\big(2\alpha+(1-\alpha)\gamma\big) + \sum'_{n}\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_n)$, where the tail is a single `tsum` over all $n\in\mathbb{N}$ whose $n=0$ term is $0$, whose $n=1$ term is $\pi_\alpha(\mathrm{lead}_1)\cdot 2\big((1-\alpha)\gamma+(1-\alpha)(1-\gamma)\big)$, and whose terms for $n\ge 2$ are $\pi_\alpha(\mathrm{lead}_n)\big((1-\alpha)\gamma+(1-\alpha)(1-\gamma)\big)$; this `tsum` is $0$ if that family is not summable.

**Right-hand side.** Three explicit terms: the $\mathrm{tie}$ term with coefficient $2\alpha+\gamma(1-\alpha)$; the $\mathrm{lead}_1$ term with coefficient $2(1-\alpha)$; and a *separate* `tsum` over $n\in\mathbb{N}$ of $\pi_\alpha(\mathrm{lead}_{n+2})$ (the lead states of index $\ge 2$), multiplied by $(1-\alpha)$. This second `tsum` is likewise $0$ if the family $n\mapsto\pi_\alpha(\mathrm{lead}_{n+2})$ is not summable. The two sides therefore involve two different `tsum`s, each with its own summability convention, and the statement equates them after the finite bookkeeping above. The right-hand side uses the factor $(1-\alpha)$ where the left-hand side has $(1-\alpha)\gamma+(1-\alpha)(1-\gamma)$.

**$\pi_\alpha$.** The custom family `stationary` $\alpha$: $\pi_\alpha(\mathrm{zero})=(1-2\alpha)/D(\alpha)$, $\pi_\alpha(\mathrm{tie})=(1-\alpha)(\alpha-2\alpha^2)/D(\alpha)$, $\pi_\alpha(\mathrm{lead}_n)=(\alpha/(1-\alpha))^n(\alpha-2\alpha^2)/D(\alpha)$, $D(\alpha)=2\alpha^3-4\alpha^2+1$, real division by zero equal to $0$ (if $D(\alpha)=0$ both sides are $0$). Under the hypotheses $1-\alpha\ne 0$. The identity is asserted for every $\alpha\in(0,\tfrac12)$ and every real $\gamma$.
