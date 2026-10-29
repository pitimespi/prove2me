## The claim

The selfish-mining mission took the stationary distribution of Eyal and Sirer's equation (7) as a definition and proved it is invariant with total mass 1. That leaves a gap a careful reader will point out: the revenue analysis is only meaningful if the chain has no other stationary distribution. This mission closes it: every nonnegative, lead-summable, mass-one function that is invariant under one step of the chain is the paper's distribution.

## What is proved

- **Stationarity** (`stationary_isStationary`): the paper's distribution satisfies the predicate.
- **Balance for any stationary π** (`balance_zero_of`, `balance_tie_of`, `balance_one_of`, `balance_two_of`, `balance_lead_of`): the five balance identities follow from invariance alone, for every $\alpha$ and $\gamma$.
- **Geometric form** (`geometric_of_isStationary`): on the lead states every stationary distribution is geometric with ratio $\alpha/(1-\alpha)$; the recurrence's constant mode is excluded by summability.
- **Uniqueness** (`stationary_unique`, the goal): every stationary distribution equals `stationary α` state by state.

## What this rests on and what it does not say

The hypotheses $0 < \alpha < 1/2$ are essential: for $\alpha \ge 1/2$ the chain is not positive recurrent and no such distribution exists. Nonnegativity of $\pi$ is in the predicate for faithfulness to the notion of a distribution but is not needed by the proof. No limit theorem is proved: that the chain converges to this distribution from any start, or that time averages of the revenue process converge to the stationary rates, remains outside the formalization. ([arXiv:1311.0243](https://arxiv.org/abs/1311.0243))
