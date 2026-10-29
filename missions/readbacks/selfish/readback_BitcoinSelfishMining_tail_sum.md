# Read-back: `BitcoinSelfishMining.tail_sum`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$ (both hypotheses named and usable). Then
$$
\sum_{n=0}^{\infty}{}'\;\pi_\alpha(\mathrm{lead}_{n+2}) \;=\; \frac{\pi_\alpha(\mathrm{lead}_0)\cdot\left(\dfrac{\alpha}{1-\alpha}\right)^{2}\cdot(1-\alpha)}{1-2\alpha}.
$$
The left-hand side is Mathlib's `tsum` over $n\in\mathbb{N}$ of the values of the custom family $\pi_\alpha=$ `stationary` $\alpha$ at the states $\mathrm{lead}_2,\mathrm{lead}_3,\dots$ (i.e. the lead states with index at least $2$; the states $\mathrm{lead}_0$ and $\mathrm{lead}_1$ are excluded from the sum); it equals the sum of the series when that family is summable and $0$ otherwise. The right-hand side is parsed as $\big(\big(\pi_\alpha(\mathrm{lead}_0)\cdot(\alpha/(1-\alpha))^2\big)\cdot(1-\alpha)\big)\,/\,(1-2\alpha)$; under $\alpha<\tfrac12$ both $1-\alpha$ and $1-2\alpha$ are non-zero, so these divisions are genuine.

Unfolding $\pi_\alpha(\mathrm{lead}_m) = (\alpha/(1-\alpha))^m\cdot c$ with $c = (\alpha-2\alpha^2)/D(\alpha)$, $D(\alpha)=2\alpha^3-4\alpha^2+1$ (real division by zero equal to $0$, so $c=0$ if $D(\alpha)=0$) and $\rho=\alpha/(1-\alpha)$, the statement reads
$$
\sum_{n=0}^{\infty}{}'\;\rho^{\,n+2}\,c \;=\; \frac{c\cdot\rho^{2}\cdot(1-\alpha)}{1-2\alpha}\qquad\text{for every }\alpha\in(0,\tfrac12).
$$
No $\gamma$ and no transition weights appear.
