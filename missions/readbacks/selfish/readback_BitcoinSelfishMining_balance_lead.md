# Read-back: `BitcoinSelfishMining.balance_lead`

Let $\alpha$ be a real number with $0 < \alpha$ and $\alpha < \tfrac12$ (both hypotheses are named and may be used in the proof), and let $n$ be any natural number $n \in \{0,1,2,\dots\}$. Then
$$
\pi_\alpha(\mathrm{lead}_{n+2}) \;=\; \alpha\cdot\pi_\alpha(\mathrm{lead}_{n+1}) \;+\; (1-\alpha)\cdot\pi_\alpha(\mathrm{lead}_{n+3}).
$$

Here $\pi_\alpha$ is the custom family `stationary` $\alpha$ on the states $\{\mathrm{zero},\mathrm{tie}\}\cup\{\mathrm{lead}_m : m\in\mathbb{N}\}$, whose values at the $\mathrm{lead}$ states are
$$
\pi_\alpha(\mathrm{lead}_m) = \left(\frac{\alpha}{1-\alpha}\right)^{m}\cdot\frac{\alpha-2\alpha^2}{D(\alpha)},\qquad D(\alpha) = 2\alpha^3-4\alpha^2+1,
$$
with real division by zero equal to $0$ (so if $D(\alpha) = 0$ every $\pi_\alpha(\mathrm{lead}_m)$ is $0$ and both sides of the equation are $0$; under the hypothesis $\alpha<\tfrac12$ the factor $1-\alpha$ is non-zero). Writing $c = (\alpha-2\alpha^2)/D(\alpha)$ and $\rho = \alpha/(1-\alpha)$, the statement unfolds to the identity
$$
\rho^{\,n+2}\,c \;=\; \alpha\,\rho^{\,n+1}\,c \;+\; (1-\alpha)\,\rho^{\,n+3}\,c
$$
for all $n\in\mathbb{N}$ and all $\alpha\in(0,\tfrac12)$. The indices $n+1$, $n+2$, $n+3$ mean that the equation is asserted only for the states $\mathrm{lead}_k$ with $k\ge 2$ on the left-hand side (never for $\mathrm{lead}_0$ or $\mathrm{lead}_1$). Only $\pi_\alpha$ at lead states appears; neither the transition function nor $\gamma$ is involved.
