# Read-back: `BitcoinSelfishMining.threshold`

Let $\alpha,\gamma$ be real numbers with the four hypotheses $0<\alpha$, $\alpha<\tfrac12$, $0\le\gamma$, $\gamma\le 1$. The hypothesis $0\le\gamma$ carries an underscore-prefixed name (`_hγ0`), signalling that the proof is not expected to use it; it is nevertheless a hypothesis of the theorem, so the claim is made only for $\gamma\in[0,1]$ (and $\alpha\in(0,\tfrac12)$). The other three are named and usable. Then the following two statements are **equivalent** (if and only if):
$$
R_{\alpha,\gamma} > \alpha \qquad\Longleftrightarrow\qquad \alpha > \tau(\gamma).
$$
Both inequalities are strict.

**$\tau(\gamma)$** is the custom `profitThreshold` $\gamma$:
$$
\tau(\gamma) = \frac{1-\gamma}{3-2\gamma},
$$
with real division by zero equal to $0$; under $\gamma\le 1$ the denominator satisfies $3-2\gamma\ge 1$, so the division is genuine. For instance $\tau(0)=\tfrac13$, $\tau(1)=0$.

**$R_{\alpha,\gamma}$** is the custom `relativeRevenue` $\alpha\,\gamma$:
$$
R_{\alpha,\gamma} = \frac{r^{\mathrm{pool}}_{\alpha,\gamma}}{r^{\mathrm{pool}}_{\alpha,\gamma}+r^{\mathrm{oth}}_{\alpha,\gamma}}\quad(=0 \text{ if the denominator is } 0),
$$
where $r^{\mathrm{pool}}_{\alpha,\gamma}$ (`poolRevenue`) and $r^{\mathrm{oth}}_{\alpha,\gamma}$ (`othersRevenue`) are the custom `stateSum`s
$$
r^{\mathrm{pool}}_{\alpha,\gamma} = \sum_{s}\pi_\alpha(s)\,g^{\mathrm{pool}}_{\alpha,\gamma}(s),\qquad r^{\mathrm{oth}}_{\alpha,\gamma} = \sum_{s}\pi_\alpha(s)\,g^{\mathrm{oth}}_{\alpha,\gamma}(s),
$$
each meaning: the value at $\mathrm{zero}$, plus the value at $\mathrm{tie}$, plus Mathlib's `tsum` over $n\in\mathbb{N}$ of the values at $\mathrm{lead}_n$ (the `tsum` being $0$ for a non-summable family). Here $\pi_\alpha$ is `stationary` $\alpha$: $\pi_\alpha(\mathrm{zero})=(1-2\alpha)/D(\alpha)$, $\pi_\alpha(\mathrm{tie})=(1-\alpha)(\alpha-2\alpha^2)/D(\alpha)$, $\pi_\alpha(\mathrm{lead}_n)=(\alpha/(1-\alpha))^n(\alpha-2\alpha^2)/D(\alpha)$, $D(\alpha)=2\alpha^3-4\alpha^2+1$, with real division by zero equal to $0$. The expected gains use the weights $p(\mathrm{pool})=\alpha$, $p(\mathrm{honestOnPool})=(1-\alpha)\gamma$, $p(\mathrm{honestOnOthers})=(1-\alpha)(1-\gamma)$ and the integer tables `poolGain` / `othersGain`, giving
$$
g^{\mathrm{pool}}(\mathrm{zero})=0,\ g^{\mathrm{pool}}(\mathrm{tie})=2\alpha+(1-\alpha)\gamma,\ g^{\mathrm{pool}}(\mathrm{lead}_0)=0,\ g^{\mathrm{pool}}(\mathrm{lead}_1)=2(1-\alpha)\gamma+2(1-\alpha)(1-\gamma),\ g^{\mathrm{pool}}(\mathrm{lead}_{m+2})=(1-\alpha)\gamma+(1-\alpha)(1-\gamma),
$$
$$
g^{\mathrm{oth}}(\mathrm{zero})=(1-\alpha)\gamma+(1-\alpha)(1-\gamma),\ g^{\mathrm{oth}}(\mathrm{tie})=(1-\alpha)\gamma+2(1-\alpha)(1-\gamma),\ g^{\mathrm{oth}}(\mathrm{lead}_n)=0 .
$$

So the theorem asserts, for every $\alpha\in(0,\tfrac12)$ and every $\gamma\in[0,1]$: the real number $R_{\alpha,\gamma}$ (as defined above via total operations) strictly exceeds $\alpha$ exactly when $\alpha$ strictly exceeds $(1-\gamma)/(3-2\gamma)$. Nothing is claimed for $\alpha\ge\tfrac12$, $\alpha\le 0$, or $\gamma\notin[0,1]$, and nothing is claimed about the case $R_{\alpha,\gamma}=\alpha$ beyond what the biconditional implies (namely that it can occur only when $\alpha\le\tau(\gamma)$).
