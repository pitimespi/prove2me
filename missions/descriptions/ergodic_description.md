## The claim

Eyal and Sirer's relative revenue is computed from the stationary distribution of their Markov chain, and the threshold result is read as "a pool above the threshold earns more than its share *over time*". The selfish-mining missions proved the formula for the stationary distribution, its uniqueness, and the threshold as statements about that distribution. This mission proves the time statement: started from no lead (or from any distribution), the chain's time-averaged occupation converges to the stationary distribution, the pool's realized revenue share converges to the paper's formula, and above the threshold it eventually exceeds the pool's hashrate.

## What is proved

- **The chain over time** (the five `dist_*` step equations, `dist_mass`, `dist_summable_lead`, `dist_nonneg`, `isDist_dist`, `isDist_distN`, `dist_stationary`, `distN_stationary`, `isDist_delta`, `le_one_of_isDist`, `distN_mix`): one step of the chain as an operator on distributions, preserving distributions, with the stationary distribution as a fixed point.
- **Tightness** (`distN_zero_lead_le`, `distN_delta_lead_le`): from any start, the probability of a long private lead is bounded geometrically, uniformly in time.
- **Cesàro convergence** (`cesaro_delta_tendsto`, `cesaro_zero_tendsto`, `cesaro_tendsto`): the average occupation of every state over the first $n$ steps converges to the stationary distribution, from any initial distribution. The proof uses the uniqueness mission: limit points are invariant with mass 1.
- **Revenue over time** (`avgPoolGain_eq`, `avgOthersGain_eq`, `avgPoolGain_tendsto`, `avgOthersGain_tendsto`, `avgRelativeRevenue_tendsto`, the goal; `avgRelativeRevenue_eventually_gt`): the time-averaged revenues converge to the paper's rates and the realized share to the relative revenue; above $(1-\gamma)/(3-2\gamma)$ the pool's realized share eventually exceeds $\alpha$.
- **Renewal structure** (`firstReturn_zero`, `last_exit`, `renewal_equation`): the last-exit decomposition and the renewal equation for returns to `zero`, with an aperiodic return-time distribution.

## What this rests on and what it does not say

Convergence is in Cesàro mean, which is what a long-run revenue share needs. Pointwise convergence of the $n$-step distributions (which holds, the chain being aperiodic) is not proved; the renewal equation is the first step towards it. "Revenue" is the expected number of credited blocks; almost-sure convergence of the realized share along a single run is not stated. ([arXiv:1311.0243](https://arxiv.org/abs/1311.0243))
