# Read-back: `BitcoinSelfishMining.threshold_gamma_zero`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$ (named, usable hypotheses). Then the following are **equivalent** (if and only if):
$$
R_{\alpha,0} > \alpha \qquad\Longleftrightarrow\qquad \alpha > \tfrac13,
$$
both inequalities strict, where $R_{\alpha,0}$ is the custom `relativeRevenue` evaluated at $\gamma=0$. The right-hand side is the literal rational constant $\tfrac13$ (the statement does not mention `profitThreshold`).

**Unfolding at $\gamma=0$.** The outcome weights become $p(\mathrm{pool})=\alpha$, $p(\mathrm{honestOnPool})=(1-\alpha)\cdot 0=0$, $p(\mathrm{honestOnOthers})=(1-\alpha)\cdot(1-0)=1-\alpha$. Then
$$
R_{\alpha,0} = \frac{r^{\mathrm{pool}}_{\alpha,0}}{r^{\mathrm{pool}}_{\alpha,0}+r^{\mathrm{oth}}_{\alpha,0}}\quad(=0\text{ if the denominator is }0),
$$
with
$$
r^{\mathrm{pool}}_{\alpha,0} = \pi_\alpha(\mathrm{zero})\cdot 0 + \pi_\alpha(\mathrm{tie})\,(2\alpha + 0\cdot 1 + (1-\alpha)\cdot 0) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{pool}}_{\alpha,0}(\mathrm{lead}_n),
$$
where $g^{\mathrm{pool}}_{\alpha,0}(\mathrm{lead}_0)=0$, $g^{\mathrm{pool}}_{\alpha,0}(\mathrm{lead}_1)=0\cdot 2+(1-\alpha)\cdot 2 = 2(1-\alpha)$, $g^{\mathrm{pool}}_{\alpha,0}(\mathrm{lead}_{m+2})=0\cdot 1+(1-\alpha)\cdot 1 = 1-\alpha$, and
$$
r^{\mathrm{oth}}_{\alpha,0} = \pi_\alpha(\mathrm{zero})\,\big(0\cdot 1 + (1-\alpha)\cdot 1\big) + \pi_\alpha(\mathrm{tie})\,\big(0\cdot 1 + (1-\alpha)\cdot 2\big) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\cdot 0 .
$$
Each $\sum'$ is Mathlib's `tsum` over $n\in\mathbb{N}$ ($0$ if the family is not summable; the all-zero family sums to $0$). $\pi_\alpha$ is `stationary` $\alpha$: $\pi_\alpha(\mathrm{zero})=(1-2\alpha)/D(\alpha)$, $\pi_\alpha(\mathrm{tie})=(1-\alpha)(\alpha-2\alpha^2)/D(\alpha)$, $\pi_\alpha(\mathrm{lead}_n)=(\alpha/(1-\alpha))^n(\alpha-2\alpha^2)/D(\alpha)$, $D(\alpha)=2\alpha^3-4\alpha^2+1$, with real division by zero equal to $0$.

So the theorem asserts that, for every $\alpha\in(0,\tfrac12)$, the real number $R_{\alpha,0}$ strictly exceeds $\alpha$ exactly when $\alpha>\tfrac13$; in particular for $\alpha\in(0,\tfrac13]$ it asserts $R_{\alpha,0}\le\alpha$. Nothing is said about $\alpha$ outside $(0,\tfrac12)$.
