# Read-back: `BitcoinSelfishMining.total_mass`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$ (both hypotheses named and usable). Then
$$
\pi_\alpha(\mathrm{zero}) + \pi_\alpha(\mathrm{tie}) + \sum_{n=0}^{\infty}{}'\;\pi_\alpha(\mathrm{lead}_n) \;=\; 1,
$$
where the left-hand side is the custom `stateSum` of the custom family $\pi_\alpha =$ `stationary` $\alpha$, and the tail is Mathlib's `tsum` over $n\in\mathbb{N}$, which equals the sum of the series when the family $n\mapsto\pi_\alpha(\mathrm{lead}_n)$ is summable and equals $0$ otherwise. Unfolding $\pi_\alpha$,
$$
\frac{1-2\alpha}{D(\alpha)} + \frac{(1-\alpha)(\alpha-2\alpha^2)}{D(\alpha)} + \sum_{n=0}^{\infty}{}'\left(\frac{\alpha}{1-\alpha}\right)^{n}\frac{\alpha-2\alpha^2}{D(\alpha)} \;=\; 1,
\qquad D(\alpha)=2\alpha^3-4\alpha^2+1,
$$
with real division by zero equal to $0$. Under the hypotheses, $1-\alpha\ne 0$, so $\alpha/(1-\alpha)$ is a genuine quotient; the statement does not itself assume $D(\alpha)\ne 0$ (if it were $0$ the left-hand side would be $0$). The assertion is for every $\alpha\in(0,\tfrac12)$ only; $\gamma$ does not appear.
