SRC = ("I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, "
       "arXiv:1311.0243, Section 4, equation (7) (the stationary distribution): https://arxiv.org/abs/1311.0243; "
       "the selfish-mining mission's BitcoinSelfishMining (State, P, stateSum, stationary)")
TAGS = ["bitcoin", "selfish-mining", "markov-chain", "stationary-distribution", "uniqueness", "eyal-sirer", "formal-verification", "mathlib"]

DEFINITION = {
    "definition_name": "BitcoinSelfishUnique",
    "definition_title": "Stationary distributions of the selfish-mining chain",
    "natural_language_statement": r"""One predicate over the selfish-mining mission's chain.

**`IsStationary α γ π`** — a function $\pi$ from states to reals is a stationary distribution of the chain with parameters $\alpha, \gamma$: it is nonnegative on every state; its values on the lead states $\pi(\text{lead } n)$ form a summable sequence; its total mass `stateSum π` $= \pi(\text{zero}) + \pi(\text{tie}) + \sum'_n \pi(\text{lead } n)$ is 1; and it is invariant under one step: for every state $s$, $\pi(s) = $ `stateSum (fun t => π t * P α γ t s)`, the inflow into $s$ from all states weighted by the one-step transition probabilities.

**Formalization Note.** Imports Mathlib and the selfish-mining mission's definitions. The selfish-mining mission proved that its `stationary α` satisfies the balance equations and has mass 1; this mission is about every $\pi$ satisfying them.""",
}

THEOREMS = {
"BitcoinSelfishUnique.stationary_isStationary": dict(title="The paper's distribution is a stationary distribution", nl=r"""For $0 < \alpha < 1/2$ and any $\gamma$: `IsStationary α γ (stationary α)`. Nonnegativity, summability over the leads, total mass 1 and invariance, re-proved from the definitions.""", ms=None),
"BitcoinSelfishUnique.balance_zero_of": dict(title="Balance at state 0 for any stationary distribution", nl=r"""For any $\alpha, \gamma$ and any $\pi$ with `IsStationary α γ π`: $\pi_0 = (1-\alpha)\pi_0 + \pi_{0'} + (1-\alpha)\pi_2$ (with $\pi_2 = \pi(\text{lead } 1)$). Only invariance is used.""", ms=None),
"BitcoinSelfishUnique.balance_tie_of": dict(title="Balance at state 0' for any stationary distribution", nl=r"""Under the same hypotheses: $\pi_{0'} = (1-\alpha)\pi_1$.""", ms=None),
"BitcoinSelfishUnique.balance_one_of": dict(title="Balance at state 1 for any stationary distribution", nl=r"""Under the same hypotheses: $\pi_1 = \alpha\pi_0$.""", ms=None),
"BitcoinSelfishUnique.balance_two_of": dict(title="Balance at state 2 for any stationary distribution", nl=r"""Under the same hypotheses: $\pi_2 = \alpha\pi_1 + (1-\alpha)\pi_3$.""", ms=None),
"BitcoinSelfishUnique.balance_lead_of": dict(title="Balance at states k ≥ 3 for any stationary distribution", nl=r"""Under the same hypotheses, for every $n$: $\pi_{n+3} = \alpha\pi_{n+2} + (1-\alpha)\pi_{n+4}$.""", ms=("The balance equations hold for every stationary π", "Each target state's inflow is a finite sum (at most three sources); the tie row of the transition matrix sums to 1 for every γ.")),
"BitcoinSelfishUnique.geometric_of_isStationary": dict(title="Every stationary distribution is geometric on the leads", nl=r"""For $0 < \alpha < 1/2$ and `IsStationary α γ π`: for every $n$, $\pi(\text{lead}(n+1)) = \frac{\alpha}{1-\alpha}\,\pi(\text{lead } n)$. The second-order balance recurrence has the general solution $A + B r^n$ with $r = \alpha/(1-\alpha)$; summability forces $A = 0$.""", ms=("Summability kills the constant mode", "$q_n = \pi_{n+1} - r\pi_n$ is constant along the recurrence; a nonzero constant makes $\pi_n$ converge to a nonzero limit, contradicting that the terms of a summable series tend to 0.")),
"BitcoinSelfishUnique.stationary_unique": dict(title="The stationary distribution is unique", nl=r"""For $0 < \alpha < 1/2$, any $\gamma$, and any $\pi$ with `IsStationary α γ π`: $\pi(s) = $ `stationary α s` for every state $s$. With the geometric form, the balance equations at $0'$ and $1$ express every value through $\pi_0$, and total mass 1 fixes $\pi_0 = (1-2\alpha)/(2\alpha^3 - 4\alpha^2 + 1)$, the paper's equation (7). Together with the selfish-mining mission this makes the revenue analysis a statement about the chain's only stationary distribution.""", ms=None),
}
ORDER = ["BitcoinSelfishUnique.stationary_isStationary", "BitcoinSelfishUnique.balance_zero_of", "BitcoinSelfishUnique.balance_tie_of",
         "BitcoinSelfishUnique.balance_one_of", "BitcoinSelfishUnique.balance_two_of", "BitcoinSelfishUnique.balance_lead_of",
         "BitcoinSelfishUnique.geometric_of_isStationary", "BitcoinSelfishUnique.stationary_unique"]
