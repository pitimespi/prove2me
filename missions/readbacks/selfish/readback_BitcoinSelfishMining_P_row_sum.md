# Read-back: `BitcoinSelfishMining.P_row_sum`

For **every** real number $\alpha$ and **every** real number $\gamma$ (no constraints whatsoever: they may be negative, larger than $1$, etc.), and for every state $s$ of the type `State` $= \{\mathrm{zero}, \mathrm{tie}\} \cup \{\mathrm{lead}_n : n \in \mathbb{N}\}$, the following real number equals $1$:
$$
P_{\alpha,\gamma}(s,\mathrm{zero}) + P_{\alpha,\gamma}(s,\mathrm{tie}) + \sum_{n=0}^{\infty}{}'\, P_{\alpha,\gamma}(s,\mathrm{lead}_n) \;=\; 1 .
$$

Here $P_{\alpha,\gamma}(s,t)$ is the custom one-step weight from $s$ to $t$, defined as the three-term sum over the outcomes $o \in \{\mathrm{pool}, \mathrm{honestOnPool}, \mathrm{honestOnOthers}\}$ of $p_{\alpha,\gamma}(o)$ when $\mathrm{step}(s,o) = t$ and $0$ otherwise, where $p_{\alpha,\gamma}(\mathrm{pool}) = \alpha$, $p_{\alpha,\gamma}(\mathrm{honestOnPool}) = (1-\alpha)\gamma$, $p_{\alpha,\gamma}(\mathrm{honestOnOthers}) = (1-\alpha)(1-\gamma)$, and $\mathrm{step}$ is the deterministic table: $\mathrm{zero} \xrightarrow{\mathrm{pool}} \mathrm{lead}_0$, $\mathrm{zero} \xrightarrow{\text{other}} \mathrm{zero}$; $\mathrm{tie} \xrightarrow{\text{any}} \mathrm{zero}$; $\mathrm{lead}_0 \xrightarrow{\mathrm{pool}} \mathrm{lead}_1$, $\mathrm{lead}_0 \xrightarrow{\text{other}} \mathrm{tie}$; $\mathrm{lead}_1 \xrightarrow{\mathrm{pool}} \mathrm{lead}_2$, $\mathrm{lead}_1 \xrightarrow{\text{other}} \mathrm{zero}$; $\mathrm{lead}_{n+2} \xrightarrow{\mathrm{pool}} \mathrm{lead}_{n+3}$, $\mathrm{lead}_{n+2} \xrightarrow{\text{other}} \mathrm{lead}_{n+1}$ ("other" meaning either honest outcome).

The left-hand side is the custom `stateSum` of the function $t \mapsto P_{\alpha,\gamma}(s,t)$: the value at $\mathrm{zero}$, plus the value at $\mathrm{tie}$, plus Mathlib's `tsum` over $n\in\mathbb{N}$ of the values at $\mathrm{lead}_n$ (a `tsum` is $0$ for a non-summable family). For each fixed $s$, by the table above at most two indices $n$ give a non-zero term $P_{\alpha,\gamma}(s,\mathrm{lead}_n)$, so the tail family has finite support and its `tsum` is an ordinary finite sum. Written out per case, the assertion is:

- $s = \mathrm{zero}$: $\big[(1-\alpha)\gamma + (1-\alpha)(1-\gamma)\big] + 0 + \alpha = 1$;
- $s = \mathrm{tie}$: $\big[\alpha + (1-\alpha)\gamma + (1-\alpha)(1-\gamma)\big] + 0 + 0 = 1$;
- $s = \mathrm{lead}_0$: $0 + \big[(1-\alpha)\gamma + (1-\alpha)(1-\gamma)\big] + \alpha = 1$;
- $s = \mathrm{lead}_1$: $\big[(1-\alpha)\gamma + (1-\alpha)(1-\gamma)\big] + 0 + \alpha = 1$;
- $s = \mathrm{lead}_{n+2}$: $0 + 0 + \big[\alpha + (1-\alpha)\gamma + (1-\alpha)(1-\gamma)\big] = 1$.

Because $\alpha$ and $\gamma$ are arbitrary reals, the statement includes, e.g., $\alpha = 5$ or $\gamma = -3$; it is a purely algebraic identity about these sums, with no probabilistic hypotheses.
