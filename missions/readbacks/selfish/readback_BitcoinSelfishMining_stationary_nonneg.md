# Read-back: `BitcoinSelfishMining.stationary_nonneg`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$ (both hypotheses named and usable), and let $s$ be any state in $\{\mathrm{zero},\mathrm{tie}\}\cup\{\mathrm{lead}_n : n\in\mathbb{N}\}$. Then
$$
0 \;\le\; \pi_\alpha(s),
$$
a non-strict inequality. Here $\pi_\alpha$ is the custom family `stationary` $\alpha$:
$$
\pi_\alpha(\mathrm{zero}) = \frac{1-2\alpha}{D(\alpha)},\qquad
\pi_\alpha(\mathrm{tie}) = \frac{(1-\alpha)(\alpha-2\alpha^2)}{D(\alpha)},\qquad
\pi_\alpha(\mathrm{lead}_n) = \left(\frac{\alpha}{1-\alpha}\right)^{n}\cdot\frac{\alpha-2\alpha^2}{D(\alpha)},
$$
with $D(\alpha)=2\alpha^3-4\alpha^2+1$ and real division by zero equal to $0$. So the statement is the conjunction of the three claims, for every $\alpha\in(0,\tfrac12)$:
$$
0\le\frac{1-2\alpha}{D(\alpha)},\qquad 0\le\frac{(1-\alpha)(\alpha-2\alpha^2)}{D(\alpha)},\qquad 0\le\left(\frac{\alpha}{1-\alpha}\right)^{n}\frac{\alpha-2\alpha^2}{D(\alpha)}\ \ \text{for all } n\in\mathbb{N}.
$$
If $D(\alpha)$ were $0$ for some such $\alpha$, each value would be $0$ by the division convention and the inequality would hold trivially there; the statement itself does not assume or assert $D(\alpha)\neq 0$. Nothing is claimed about positivity (strict), about summing to $1$, or about $\alpha$ outside $(0,\tfrac12)$.
