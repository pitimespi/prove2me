# Read-back: `BitcoinSelfishMining.balance_tie`

Let $\alpha$ be a real number with $0<\alpha$ and $\alpha<\tfrac12$. Both hypotheses are present in the statement but are given underscore-prefixed names (`_h0`, `_h1`), which signals that the proof is not expected to use them; they nonetheless remain hypotheses, so the theorem is asserted only for $\alpha\in(0,\tfrac12)$ and claims nothing outside that interval. Then
$$
\pi_\alpha(\mathrm{tie}) \;=\; (1-\alpha)\cdot\pi_\alpha(\mathrm{lead}_0).
$$

Here $\pi_\alpha$ is the custom family `stationary` $\alpha$, with
$$
\pi_\alpha(\mathrm{tie}) = \frac{(1-\alpha)(\alpha-2\alpha^2)}{D(\alpha)},\qquad
\pi_\alpha(\mathrm{lead}_0) = \left(\frac{\alpha}{1-\alpha}\right)^{0}\cdot\frac{\alpha-2\alpha^2}{D(\alpha)} = \frac{\alpha-2\alpha^2}{D(\alpha)},\qquad D(\alpha)=2\alpha^3-4\alpha^2+1,
$$
with the zeroth power equal to $1$ and real division by zero equal to $0$ (if $D(\alpha)=0$ both sides are $0$). So the statement unfolds to
$$
\frac{(1-\alpha)(\alpha-2\alpha^2)}{D(\alpha)} \;=\; (1-\alpha)\cdot\frac{\alpha-2\alpha^2}{D(\alpha)}.
$$
No transition probabilities and no $\gamma$ appear.
