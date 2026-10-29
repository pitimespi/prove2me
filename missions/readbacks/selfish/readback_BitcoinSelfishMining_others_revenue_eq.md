# Read-back: `BitcoinSelfishMining.others_revenue_eq`

For **every** real $\alpha$ and **every** real $\gamma$, with **no hypotheses whatsoever** (no positivity, no upper bound, no restriction to $[0,1]$),
$$
r^{\mathrm{oth}}_{\alpha,\gamma} \;=\; \pi_\alpha(\mathrm{tie})\cdot\big((1-\alpha)(1-\gamma)\cdot 2 + \gamma(1-\alpha)\cdot 1\big) \;+\; \pi_\alpha(\mathrm{zero})\cdot\big((1-\alpha)\cdot 1\big).
$$

**Left-hand side.** $r^{\mathrm{oth}}_{\alpha,\gamma}$ is the custom `othersRevenue` $\alpha\,\gamma$, defined as the custom `stateSum` of $s\mapsto \pi_\alpha(s)\,g^{\mathrm{oth}}_{\alpha,\gamma}(s)$:
$$
r^{\mathrm{oth}}_{\alpha,\gamma} = \pi_\alpha(\mathrm{zero})\,g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{zero}) + \pi_\alpha(\mathrm{tie})\,g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{tie}) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{lead}_n),
$$
where $g^{\mathrm{oth}}_{\alpha,\gamma}(s) = \sum_{o} p_{\alpha,\gamma}(o)\cdot\mathrm{othersGain}(s,o)$ over the three outcomes, with $p_{\alpha,\gamma}(\mathrm{pool})=\alpha$, $p_{\alpha,\gamma}(\mathrm{honestOnPool})=(1-\alpha)\gamma$, $p_{\alpha,\gamma}(\mathrm{honestOnOthers})=(1-\alpha)(1-\gamma)$, and $\mathrm{othersGain}$: $(\mathrm{zero},\mathrm{pool})\mapsto 0$, $(\mathrm{zero},\text{either honest})\mapsto 1$, $(\mathrm{tie},\mathrm{honestOnPool})\mapsto 1$, $(\mathrm{tie},\mathrm{honestOnOthers})\mapsto 2$, and $0$ for every other pair (in particular $(\mathrm{tie},\mathrm{pool})\mapsto 0$ and $(\mathrm{lead}_n,o)\mapsto 0$ for all $n,o$). Hence
$$
g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{zero}) = \alpha\cdot 0 + (1-\alpha)\gamma\cdot 1 + (1-\alpha)(1-\gamma)\cdot 1,\qquad
g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{tie}) = \alpha\cdot 0 + (1-\alpha)\gamma\cdot 1 + (1-\alpha)(1-\gamma)\cdot 2,\qquad
g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{lead}_n) = 0,
$$
so every term of the tail `tsum` is $0$ and the tail contributes $0$ (the zero family is summable). Thus the left-hand side equals
$$
\pi_\alpha(\mathrm{zero})\big((1-\alpha)\gamma + (1-\alpha)(1-\gamma)\big) + \pi_\alpha(\mathrm{tie})\big((1-\alpha)\gamma + 2(1-\alpha)(1-\gamma)\big).
$$

**Right-hand side.** The coefficient of $\pi_\alpha(\mathrm{tie})$ is $2(1-\alpha)(1-\gamma) + \gamma(1-\alpha)$, and the coefficient of $\pi_\alpha(\mathrm{zero})$ is $(1-\alpha)$ (written as $(1-\alpha)\cdot 1$). So, after cancelling the common $\mathrm{tie}$ coefficient, the content of the statement is that $\pi_\alpha(\mathrm{zero})\big((1-\alpha)\gamma+(1-\alpha)(1-\gamma)\big) = \pi_\alpha(\mathrm{zero})(1-\alpha)$.

**$\pi_\alpha$.** The custom family `stationary` $\alpha$: $\pi_\alpha(\mathrm{zero}) = (1-2\alpha)/D(\alpha)$, $\pi_\alpha(\mathrm{tie}) = (1-\alpha)(\alpha-2\alpha^2)/D(\alpha)$, $D(\alpha)=2\alpha^3-4\alpha^2+1$, with real division by zero equal to $0$ (if $D(\alpha)=0$ both sides are $0$). Since $\alpha,\gamma$ are arbitrary reals, the identity is asserted for all of $\mathbb{R}^2$, including values where $\pi_\alpha$ is negative or where the "weights" $p_{\alpha,\gamma}$ are negative.
