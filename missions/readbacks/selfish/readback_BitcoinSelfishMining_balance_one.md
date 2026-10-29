# Read-back: `BitcoinSelfishMining.balance_one`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$ (both hypotheses named and usable). Then
$$
\pi_\alpha(\mathrm{lead}_0) \;=\; \alpha\cdot\pi_\alpha(\mathrm{zero}).
$$

Here $\pi_\alpha$ is the custom family `stationary` $\alpha$, with
$$
\pi_\alpha(\mathrm{zero}) = \frac{1-2\alpha}{D(\alpha)},\qquad
\pi_\alpha(\mathrm{lead}_0) = \left(\frac{\alpha}{1-\alpha}\right)^{0}\cdot\frac{\alpha-2\alpha^2}{D(\alpha)} = \frac{\alpha-2\alpha^2}{D(\alpha)},\qquad D(\alpha)=2\alpha^3-4\alpha^2+1,
$$
where the zeroth power is $1$ regardless of the base, and real division by zero is $0$ (if $D(\alpha)=0$ both sides are $0$). So the statement unfolds to
$$
\frac{\alpha-2\alpha^2}{D(\alpha)} \;=\; \alpha\cdot\frac{1-2\alpha}{D(\alpha)}\qquad\text{for every }\alpha\in(0,\tfrac12).
$$
No transition probabilities and no $\gamma$ appear in the statement.
