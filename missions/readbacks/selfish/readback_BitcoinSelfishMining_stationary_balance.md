# Read-back: `BitcoinSelfishMining.stationary_balance`

Let $\alpha$ and $\gamma$ be real numbers, with the hypotheses $0<\alpha$ and $\alpha<\tfrac12$ (named and usable) and **no hypothesis at all on $\gamma$** (it may be any real number). Let $s$ be any state in $\{\mathrm{zero},\mathrm{tie}\}\cup\{\mathrm{lead}_n : n\in\mathbb{N}\}$. Then
$$
\pi_\alpha(s) \;=\; \pi_\alpha(\mathrm{zero})\,P_{\alpha,\gamma}(\mathrm{zero},s) \;+\; \pi_\alpha(\mathrm{tie})\,P_{\alpha,\gamma}(\mathrm{tie},s) \;+\; \sum_{n=0}^{\infty}{}'\;\pi_\alpha(\mathrm{lead}_n)\,P_{\alpha,\gamma}(\mathrm{lead}_n,s).
$$
The right-hand side is the custom `stateSum` of the function $t\mapsto \pi_\alpha(t)\,P_{\alpha,\gamma}(t,s)$: value at $\mathrm{zero}$, plus value at $\mathrm{tie}$, plus Mathlib's `tsum` over $n\in\mathbb{N}$ of the values at $\mathrm{lead}_n$ (a `tsum` is $0$ for a non-summable family). Note the order of arguments: the second factor is the weight *from* $t$ *to* the fixed $s$.

**Ingredients.** $\pi_\alpha$ is the custom family `stationary` $\alpha$:
$$
\pi_\alpha(\mathrm{zero}) = \frac{1-2\alpha}{D(\alpha)},\quad
\pi_\alpha(\mathrm{tie}) = \frac{(1-\alpha)(\alpha-2\alpha^2)}{D(\alpha)},\quad
\pi_\alpha(\mathrm{lead}_n) = \left(\frac{\alpha}{1-\alpha}\right)^{n}\frac{\alpha-2\alpha^2}{D(\alpha)},\quad D(\alpha)=2\alpha^3-4\alpha^2+1,
$$
with real division by zero equal to $0$. $P_{\alpha,\gamma}(t,s)$ is the sum over the three outcomes $o$ of $p_{\alpha,\gamma}(o)$ if $\mathrm{step}(t,o)=s$ and $0$ otherwise, where $p_{\alpha,\gamma}(\mathrm{pool})=\alpha$, $p_{\alpha,\gamma}(\mathrm{honestOnPool})=(1-\alpha)\gamma$, $p_{\alpha,\gamma}(\mathrm{honestOnOthers})=(1-\alpha)(1-\gamma)$, and $\mathrm{step}$ is: $\mathrm{zero}\xrightarrow{\mathrm{pool}}\mathrm{lead}_0$, $\mathrm{zero}\xrightarrow{\text{other}}\mathrm{zero}$; $\mathrm{tie}\xrightarrow{\text{any}}\mathrm{zero}$; $\mathrm{lead}_0\xrightarrow{\mathrm{pool}}\mathrm{lead}_1$, $\mathrm{lead}_0\xrightarrow{\text{other}}\mathrm{tie}$; $\mathrm{lead}_1\xrightarrow{\mathrm{pool}}\mathrm{lead}_2$, $\mathrm{lead}_1\xrightarrow{\text{other}}\mathrm{zero}$; $\mathrm{lead}_{n+2}\xrightarrow{\mathrm{pool}}\mathrm{lead}_{n+3}$, $\mathrm{lead}_{n+2}\xrightarrow{\text{other}}\mathrm{lead}_{n+1}$. Write $h := (1-\alpha)\gamma+(1-\alpha)(1-\gamma)$ for the sum of the two "honest" weights (algebraically equal to $1-\alpha$ for all real $\gamma$).

**Unfolded per case of $s$.** For each fixed $s$ only finitely many $t$ have $P_{\alpha,\gamma}(t,s)\ne 0$, so the tail `tsum` is a finite sum and the statement reads:

- $s=\mathrm{zero}$: $\ \pi_\alpha(\mathrm{zero}) = \pi_\alpha(\mathrm{zero})\,h + \pi_\alpha(\mathrm{tie})\,(\alpha+h) + \pi_\alpha(\mathrm{lead}_1)\,h$;
- $s=\mathrm{tie}$: $\ \pi_\alpha(\mathrm{tie}) = \pi_\alpha(\mathrm{lead}_0)\,h$;
- $s=\mathrm{lead}_0$: $\ \pi_\alpha(\mathrm{lead}_0) = \pi_\alpha(\mathrm{zero})\,\alpha$;
- $s=\mathrm{lead}_1$: $\ \pi_\alpha(\mathrm{lead}_1) = \pi_\alpha(\mathrm{lead}_0)\,\alpha + \pi_\alpha(\mathrm{lead}_2)\,h$;
- $s=\mathrm{lead}_{m+2}$ ($m\in\mathbb{N}$): $\ \pi_\alpha(\mathrm{lead}_{m+2}) = \pi_\alpha(\mathrm{lead}_{m+1})\,\alpha + \pi_\alpha(\mathrm{lead}_{m+3})\,h$.

These are asserted simultaneously for every $s$, every $\alpha\in(0,\tfrac12)$ and every real $\gamma$. If $D(\alpha)=0$, all values of $\pi_\alpha$ are $0$ and every equation reads $0=0$.
