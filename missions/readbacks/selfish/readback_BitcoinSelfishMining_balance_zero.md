# Read-back: `BitcoinSelfishMining.balance_zero`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$ (both hypotheses named and usable). Then
$$
\pi_\alpha(\mathrm{zero}) \;=\; (1-\alpha)\cdot\pi_\alpha(\mathrm{zero}) \;+\; \pi_\alpha(\mathrm{tie}) \;+\; (1-\alpha)\cdot\pi_\alpha(\mathrm{lead}_1).
$$
Note the middle term $\pi_\alpha(\mathrm{tie})$ carries coefficient $1$ (not $\alpha$, not $1-\alpha$).

Here $\pi_\alpha$ is the custom family `stationary` $\alpha$:
$$
\pi_\alpha(\mathrm{zero}) = \frac{1-2\alpha}{D(\alpha)},\qquad
\pi_\alpha(\mathrm{tie}) = \frac{(1-\alpha)(\alpha-2\alpha^2)}{D(\alpha)},\qquad
\pi_\alpha(\mathrm{lead}_1) = \frac{\alpha}{1-\alpha}\cdot\frac{\alpha-2\alpha^2}{D(\alpha)},
$$
with $D(\alpha)=2\alpha^3-4\alpha^2+1$ and real division by zero equal to $0$ (if $D(\alpha)=0$ every term is $0$ and the equation reads $0=0$). So the statement unfolds to
$$
\frac{1-2\alpha}{D(\alpha)} \;=\; (1-\alpha)\frac{1-2\alpha}{D(\alpha)} + \frac{(1-\alpha)(\alpha-2\alpha^2)}{D(\alpha)} + (1-\alpha)\frac{\alpha}{1-\alpha}\cdot\frac{\alpha-2\alpha^2}{D(\alpha)}
\qquad\text{for every }\alpha\in(0,\tfrac12).
$$
No transition probabilities and no $\gamma$ appear.
