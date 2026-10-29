# Read-back: `BitcoinSelfishMining.threshold_gamma_one`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$ (named, usable hypotheses). Then
$$
R_{\alpha,1} > \alpha,
$$
a strict inequality, where $R_{\alpha,1}$ is the custom `relativeRevenue` evaluated at $\gamma=1$. This is an unconditional claim for every $\alpha\in(0,\tfrac12)$ (no biconditional, no threshold on the right-hand side).

**Unfolding at $\gamma=1$.** The outcome weights become $p(\mathrm{pool})=\alpha$, $p(\mathrm{honestOnPool})=(1-\alpha)\cdot 1 = 1-\alpha$, $p(\mathrm{honestOnOthers})=(1-\alpha)\cdot(1-1)=0$. Then
$$
R_{\alpha,1} = \frac{r^{\mathrm{pool}}_{\alpha,1}}{r^{\mathrm{pool}}_{\alpha,1}+r^{\mathrm{oth}}_{\alpha,1}}\quad(=0\text{ if the denominator is }0),
$$
with
$$
r^{\mathrm{pool}}_{\alpha,1} = \pi_\alpha(\mathrm{zero})\cdot 0 + \pi_\alpha(\mathrm{tie})\,(2\alpha + (1-\alpha)) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{pool}}_{\alpha,1}(\mathrm{lead}_n),
$$
where $g^{\mathrm{pool}}_{\alpha,1}(\mathrm{lead}_0)=0$, $g^{\mathrm{pool}}_{\alpha,1}(\mathrm{lead}_1)=2(1-\alpha)\cdot 1 + 2\cdot 0 = 2(1-\alpha)$, $g^{\mathrm{pool}}_{\alpha,1}(\mathrm{lead}_{m+2})=(1-\alpha)\cdot 1 + 0 = 1-\alpha$, and
$$
r^{\mathrm{oth}}_{\alpha,1} = \pi_\alpha(\mathrm{zero})\,\big((1-\alpha)\cdot 1 + 0\cdot 1\big) + \pi_\alpha(\mathrm{tie})\,\big((1-\alpha)\cdot 1 + 0\cdot 2\big) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\cdot 0 .
$$
Each $\sum'$ is Mathlib's `tsum` over $n\in\mathbb{N}$ ($0$ if the family is not summable; the all-zero family sums to $0$). $\pi_\alpha$ is `stationary` $\alpha$: $\pi_\alpha(\mathrm{zero})=(1-2\alpha)/D(\alpha)$, $\pi_\alpha(\mathrm{tie})=(1-\alpha)(\alpha-2\alpha^2)/D(\alpha)$, $\pi_\alpha(\mathrm{lead}_n)=(\alpha/(1-\alpha))^n(\alpha-2\alpha^2)/D(\alpha)$, $D(\alpha)=2\alpha^3-4\alpha^2+1$, with real division by zero equal to $0$. The statement claims that the resulting real number $R_{\alpha,1}$ is strictly greater than $\alpha$ for every $\alpha$ in the open interval $(0,\tfrac12)$; nothing is said for other $\alpha$.
