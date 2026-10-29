# Read-back: `BitcoinSelfishMining.balance_two`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$ (both hypotheses named and usable). Then
$$
\pi_\alpha(\mathrm{lead}_1) \;=\; \alpha\cdot\pi_\alpha(\mathrm{lead}_0) \;+\; (1-\alpha)\cdot\pi_\alpha(\mathrm{lead}_2).
$$

Here $\pi_\alpha$ is the custom family `stationary` $\alpha$, whose lead values are
$$
\pi_\alpha(\mathrm{lead}_m) = \left(\frac{\alpha}{1-\alpha}\right)^{m}\cdot\frac{\alpha-2\alpha^2}{D(\alpha)},\qquad D(\alpha)=2\alpha^3-4\alpha^2+1,
$$
with real division by zero equal to $0$ (if $D(\alpha)=0$ every term is $0$). Writing $c=(\alpha-2\alpha^2)/D(\alpha)$ and $\rho=\alpha/(1-\alpha)$ (well defined as a genuine quotient since $\alpha<\tfrac12$ gives $1-\alpha\neq 0$), the statement unfolds to
$$
\rho\,c \;=\; \alpha\cdot c \;+\; (1-\alpha)\,\rho^{2}\,c \qquad\text{for every }\alpha\in(0,\tfrac12).
$$
No transition probabilities and no $\gamma$ appear.
