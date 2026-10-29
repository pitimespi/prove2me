## The claim

Eyal and Sirer (2014) showed that a mining pool can earn more than its share of the hashrate by withholding blocks: the pool's revenue share under the selfish strategy exceeds $\alpha$ exactly when $\alpha > (1-\gamma)/(3-2\gamma)$, where $\gamma$ is the fraction of honest hashrate that mines on the pool's block during a tie. The result is usually quoted as "selfish mining pays above one third of the hashrate" ($\gamma = 0$) and "any pool with network advantage can profit" ($\gamma = 1$). This mission states the paper's Markov chain and proves the paper's analysis in full.

## What is proved

- **The chain** (`P_row_sum`, `stationary_balance`, `total_mass`, with the five explicit balance identities and `stationary_nonneg`, `denominator_pos`): the transition structure of Figure 1 is stochastic, and the distribution of equation (7) is a genuine stationary probability distribution for it, derived from the transitions rather than postulated.
- **The revenues** (`tail_sum`, `pool_revenue_eq`, `others_revenue_eq`, `relative_revenue`): the revenue rates, defined as sums over the whole state space with a genuine infinite tail, reduce to equations (8), (9) and the closed form (10).
- **The threshold** (`threshold`, the goal; `threshold_gamma_zero`, `threshold_gamma_one`): the relative revenue exceeds $\alpha$ iff $\alpha$ exceeds $(1-\gamma)/(3-2\gamma)$, for $0 < \alpha < 1/2$ and $\gamma \le 1$; in particular above $1/3$ for $\gamma = 0$, and always for $\gamma = 1$.

## What this rests on and what it does not say

The model is the paper's: one block per step, the pool's reward counted as in equations (8)–(9), no propagation delay beyond $\gamma$, no difficulty adjustment. The stationary distribution is verified, not shown unique, and no ergodic theorem is proved: "revenue share" means the stationary expected revenue ratio, as in the paper. The case $\alpha \ge 1/2$ is excluded by hypothesis. ([arXiv:1311.0243](https://arxiv.org/abs/1311.0243))
