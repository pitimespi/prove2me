# Read-back: `BitcoinSelfishMining.relative_revenue`

Let $\alpha,\gamma$ be real numbers with $0<\alpha$ and $\alpha<\tfrac12$ (named, usable hypotheses) and **no hypothesis on $\gamma$** (any real). Then
$$
R_{\alpha,\gamma} \;=\; C(\alpha,\gamma),
$$
where both sides are custom quantities, unfolded as follows.

**Left-hand side** $R_{\alpha,\gamma}$ is `relativeRevenue` $\alpha\,\gamma$:
$$
R_{\alpha,\gamma} = \frac{r^{\mathrm{pool}}_{\alpha,\gamma}}{r^{\mathrm{pool}}_{\alpha,\gamma} + r^{\mathrm{oth}}_{\alpha,\gamma}},\qquad\text{equal to } 0 \text{ if } r^{\mathrm{pool}}_{\alpha,\gamma}+r^{\mathrm{oth}}_{\alpha,\gamma}=0,
$$
with
$$
r^{\mathrm{pool}}_{\alpha,\gamma} = \pi_\alpha(\mathrm{zero})\,g^{\mathrm{pool}}(\mathrm{zero}) + \pi_\alpha(\mathrm{tie})\,g^{\mathrm{pool}}(\mathrm{tie}) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{pool}}(\mathrm{lead}_n),\qquad
r^{\mathrm{oth}}_{\alpha,\gamma} = \pi_\alpha(\mathrm{zero})\,g^{\mathrm{oth}}(\mathrm{zero}) + \pi_\alpha(\mathrm{tie})\,g^{\mathrm{oth}}(\mathrm{tie}) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{oth}}(\mathrm{lead}_n),
$$
each tail being Mathlib's `tsum` (equal to $0$ when the family is not summable). Here $\pi_\alpha$ is `stationary` $\alpha$: $\pi_\alpha(\mathrm{zero})=(1-2\alpha)/D(\alpha)$, $\pi_\alpha(\mathrm{tie})=(1-\alpha)(\alpha-2\alpha^2)/D(\alpha)$, $\pi_\alpha(\mathrm{lead}_n)=(\alpha/(1-\alpha))^n(\alpha-2\alpha^2)/D(\alpha)$ with $D(\alpha)=2\alpha^3-4\alpha^2+1$ and real division by zero equal to $0$. The per-state expected gains (dropping the subscript $\alpha,\gamma$) are, with weights $p(\mathrm{pool})=\alpha$, $p(\mathrm{honestOnPool})=(1-\alpha)\gamma$, $p(\mathrm{honestOnOthers})=(1-\alpha)(1-\gamma)$:
$$
g^{\mathrm{pool}}(\mathrm{zero})=0,\ g^{\mathrm{pool}}(\mathrm{tie})=2\alpha+(1-\alpha)\gamma,\ g^{\mathrm{pool}}(\mathrm{lead}_0)=0,\ g^{\mathrm{pool}}(\mathrm{lead}_1)=2(1-\alpha)\gamma+2(1-\alpha)(1-\gamma),\ g^{\mathrm{pool}}(\mathrm{lead}_{m+2})=(1-\alpha)\gamma+(1-\alpha)(1-\gamma);
$$
$$
g^{\mathrm{oth}}(\mathrm{zero})=(1-\alpha)\gamma+(1-\alpha)(1-\gamma),\ g^{\mathrm{oth}}(\mathrm{tie})=(1-\alpha)\gamma+2(1-\alpha)(1-\gamma),\ g^{\mathrm{oth}}(\mathrm{lead}_n)=0 .
$$

**Right-hand side** $C(\alpha,\gamma)$ is `closedForm` $\alpha\,\gamma$:
$$
C(\alpha,\gamma) = \frac{\alpha(1-\alpha)^2\big(4\alpha+\gamma(1-2\alpha)\big) - \alpha^3}{1-\alpha\big(1+(2-\alpha)\alpha\big)},
$$
whose denominator expands to $1-\alpha-2\alpha^2+\alpha^3$ (a different polynomial from $D(\alpha)$), and which is $0$ by the division convention whenever that denominator vanishes.

The equality is asserted for every $\alpha\in(0,\tfrac12)$ and every real $\gamma$, including $\gamma$ outside $[0,1]$. It is an equality of two real numbers each of which is defined via total operations (division by zero giving $0$, non-summable `tsum` giving $0$), so no side condition about non-vanishing denominators or summability is part of the claim.
