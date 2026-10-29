SRC = ("I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, "
       "arXiv:1311.0243, Section 4 (Figure 1, equations (7)-(11)): https://arxiv.org/abs/1311.0243")
TAGS = ["bitcoin", "selfish-mining", "mining", "markov-chain", "game-theory", "eyal-sirer", "formal-verification", "mathlib"]

DEFINITION = {
    "definition_name": "BitcoinSelfishMining",
    "definition_title": "The Eyal–Sirer selfish-mining chain: states, transitions, stationary distribution, revenues and threshold",
    "natural_language_statement": r"""The model of Eyal and Sirer's Section 4, over Mathlib's reals. A pool with hashrate fraction $\alpha$ mines selfishly; of the honest hashrate $1-\alpha$, a fraction $\gamma$ mines on the pool's block during a tie.

**States.** `State.zero` (no private lead), `State.tie` (the paper's $0'$: a public fork of two equal branches), and `State.lead n`, a private lead of $n+1$ blocks (`lead 0` is the paper's state 1, `lead 1` state 2, `lead (n+2)` state $n+3$). **Outcomes** of a step: `pool` (probability $\alpha$), `honestOnPool` ($(1-\alpha)\gamma$), `honestOnOthers` ($(1-\alpha)(1-\gamma)$); `outcomeProb` and `outcomeSum` name these.

**`step s o`** is the transition of Figure 1: from `zero` a pool block gives `lead 0`, an honest block stays; from `lead 0` a pool block gives `lead 1`, an honest block gives `tie`; from `tie` every outcome returns to `zero`; from `lead 1` a pool block gives `lead 2`, an honest block returns to `zero`; from `lead (n+2)` a pool block gives `lead (n+3)`, an honest block `lead (n+1)`. **`poolGain`, `othersGain`** are the blocks credited at each transition (equations (8), (9)): at a tie the pool gets 2 for its own block and 1 when honest miners extend its branch, the honest miners get 1 in that case and 2 when they win the tie; honest miners get 1 for a block found in `zero`; the pool gets 2 when an honest block reduces its lead of 2 and 1 when it reduces a lead of at least 3.

**`P α γ s t`** is the one-step transition probability; **`poolExpGain`, `othersExpGain`** the expected credited blocks from a state. **`stateSum f`** $= f(\text{zero}) + f(\text{tie}) + \sum'_{n} f(\text{lead } n)$, the tail a Mathlib `tsum` (0 if not summable). **`denom α`** $= 2\alpha^3 - 4\alpha^2 + 1$; **`stationary α`** is the paper's distribution (7): $p_0 = (1-2\alpha)/\text{denom}$, $p_{0'} = (1-\alpha)(\alpha - 2\alpha^2)/\text{denom}$, $p_{\text{lead } n} = (\alpha/(1-\alpha))^n (\alpha - 2\alpha^2)/\text{denom}$. **`poolRevenue`, `othersRevenue`** are `stateSum` of $p_s$ times the expected gain; **`relativeRevenue`** $= r_{\text{pool}} / (r_{\text{pool}} + r_{\text{others}})$ (10); **`closedForm α γ`** $= \frac{\alpha(1-\alpha)^2(4\alpha + \gamma(1-2\alpha)) - \alpha^3}{1 - \alpha(1 + (2-\alpha)\alpha)}$; **`profitThreshold γ`** $= (1-\gamma)/(3-2\gamma)$ (11).

**Formalization Note.** Imports Mathlib. The stationary distribution is the paper's formula taken as a definition; its invariance and total mass are theorems. Real division by zero is 0, so `relativeRevenue` is 0 wherever the revenues sum to 0; the theorems assume $0 < \alpha < 1/2$.""",
}

THEOREMS = {
"BitcoinSelfishMining.denominator_pos": dict(title="The common denominator is positive", nl=r"""For $0 < \alpha < 1/2$: $2\alpha^3 - 4\alpha^2 + 1 > 0$.""", ms=None),
"BitcoinSelfishMining.stationary_nonneg": dict(title="The stationary probabilities are nonnegative", nl=r"""For $0 < \alpha < 1/2$ and every state $s$: `stationary α s` $\ge 0$.""", ms=None),
"BitcoinSelfishMining.P_row_sum": dict(title="The transition matrix is stochastic", nl=r"""For all real $\alpha, \gamma$ and every state $s$: `stateSum (fun t => P α γ s t) = 1`. Each row of the chain sums to one (the three outcome probabilities sum to 1 for any $\alpha, \gamma$).""", ms=None),
"BitcoinSelfishMining.balance_zero": dict(title="Balance at state 0", nl=r"""For $0 < \alpha < 1/2$: $p_0 = (1-\alpha)p_0 + p_{0'} + (1-\alpha)p_2$ (with $p_2$ = `stationary α (lead 1)`).""", ms=None),
"BitcoinSelfishMining.balance_tie": dict(title="Balance at state 0'", nl=r"""For $0 < \alpha < 1/2$: $p_{0'} = (1-\alpha)p_1$.""", ms=None),
"BitcoinSelfishMining.balance_one": dict(title="Balance at state 1", nl=r"""For $0 < \alpha < 1/2$: $p_1 = \alpha p_0$.""", ms=None),
"BitcoinSelfishMining.balance_two": dict(title="Balance at state 2", nl=r"""For $0 < \alpha < 1/2$: $p_2 = \alpha p_1 + (1-\alpha)p_3$.""", ms=None),
"BitcoinSelfishMining.balance_lead": dict(title="Balance at states k ≥ 3", nl=r"""For $0 < \alpha < 1/2$ and every $n$: $p_{n+3} = \alpha p_{n+2} + (1-\alpha) p_{n+4}$ (in the encoding, `stationary α (lead (n+2)) = α · stationary α (lead (n+1)) + (1-α) · stationary α (lead (n+3))`).""", ms=None),
"BitcoinSelfishMining.stationary_balance": dict(title="The paper's distribution is invariant for the chain", nl=r"""For $0 < \alpha < 1/2$, any $\gamma$ and every state $s$: `stationary α s = stateSum (fun t => stationary α t * P α γ t s)`. The balance equations are derived from `step` and `outcomeProb`, not postulated.""", ms=("Invariance from the transition structure", "The five explicit balance identities, each a rational-function identity after `denominator_pos`, assembled through the case analysis of `step`.")),
"BitcoinSelfishMining.tail_sum": dict(title="The tail of the distribution in closed form", nl=r"""For $0 < \alpha < 1/2$: $\sum'_{n} p_{\text{lead}(n+2)} = p_1 \left(\frac{\alpha}{1-\alpha}\right)^2 \frac{1-\alpha}{1-2\alpha}$. A geometric series with ratio $\alpha/(1-\alpha) < 1$.""", ms=None),
"BitcoinSelfishMining.total_mass": dict(title="The stationary distribution has total mass 1", nl=r"""For $0 < \alpha < 1/2$: `stateSum (stationary α) = 1`.""", ms=("A probability distribution", "`tail_sum` and `stationary_nonneg` with `denominator_pos`: the paper's (7) is a genuine stationary distribution of the chain.")),
"BitcoinSelfishMining.pool_revenue_eq": dict(title="The pool's revenue rate reduces to equation (8)", nl=r"""For $0 < \alpha < 1/2$ and any $\gamma$: `poolRevenue α γ` $= p_{0'}(2\alpha + \gamma(1-\alpha)) + p_2 \cdot 2(1-\alpha) + \left(\sum'_{n} p_{\text{lead}(n+2)}\right)(1-\alpha)$, the paper's (8) with the $k \ge 3$ tail as a `tsum`.""", ms=None),
"BitcoinSelfishMining.others_revenue_eq": dict(title="The honest revenue rate reduces to equation (9)", nl=r"""For all real $\alpha, \gamma$: `othersRevenue α γ` $= p_{0'}(2(1-\alpha)(1-\gamma) + \gamma(1-\alpha)) + p_0 (1-\alpha)$, the paper's (9).""", ms=None),
"BitcoinSelfishMining.relative_revenue": dict(title="The relative revenue equals the paper's closed form (10)", nl=r"""For $0 < \alpha < 1/2$ and any $\gamma$: `relativeRevenue α γ = closedForm α γ`, i.e. $R = \frac{\alpha(1-\alpha)^2(4\alpha + \gamma(1-2\alpha)) - \alpha^3}{1 - \alpha(1 + (2-\alpha)\alpha)}$.""", ms=("Equation (10)", "`pool_revenue_eq`, `others_revenue_eq`, `tail_sum`, then a field identity over the positive denominator.")),
"BitcoinSelfishMining.threshold": dict(title="Selfish mining beats honest mining exactly above the Eyal–Sirer threshold", nl=r"""For $0 < \alpha < 1/2$ and $0 \le \gamma \le 1$: `relativeRevenue α γ > α` if and only if $\alpha > \frac{1-\gamma}{3-2\gamma}$ (equation (11)). The pool's stationary revenue share exceeds its hashrate share exactly when its hashrate exceeds the threshold; $\gamma \ge 0$ is assumed for faithfulness but not used.""", ms=None),
"BitcoinSelfishMining.threshold_gamma_zero": dict(title="With no honest miners on the pool's branch, the threshold is 1/3", nl=r"""For $0 < \alpha < 1/2$: `relativeRevenue α 0 > α` iff $\alpha > 1/3$.""", ms=None),
"BitcoinSelfishMining.threshold_gamma_one": dict(title="With every honest miner on the pool's branch, selfish mining always pays", nl=r"""For every $0 < \alpha < 1/2$: `relativeRevenue α 1 > α`.""", ms=None),
}
ORDER = ["BitcoinSelfishMining.denominator_pos", "BitcoinSelfishMining.stationary_nonneg", "BitcoinSelfishMining.P_row_sum",
         "BitcoinSelfishMining.balance_zero", "BitcoinSelfishMining.balance_tie", "BitcoinSelfishMining.balance_one",
         "BitcoinSelfishMining.balance_two", "BitcoinSelfishMining.balance_lead", "BitcoinSelfishMining.stationary_balance",
         "BitcoinSelfishMining.tail_sum", "BitcoinSelfishMining.total_mass", "BitcoinSelfishMining.pool_revenue_eq",
         "BitcoinSelfishMining.others_revenue_eq", "BitcoinSelfishMining.relative_revenue", "BitcoinSelfishMining.threshold",
         "BitcoinSelfishMining.threshold_gamma_zero", "BitcoinSelfishMining.threshold_gamma_one"]
