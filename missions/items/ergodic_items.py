SRC = ("I. Eyal, E. G. Sirer, Majority is not Enough: Bitcoin Mining is Vulnerable, Financial Cryptography 2014, arXiv:1311.0243, Section 4 "
       "(the revenue as a long-run share); the selfish-mining missions BitcoinSelfishMining (chain, revenues, threshold) and BitcoinSelfishUnique "
       "(uniqueness of the stationary distribution); standard Markov-chain theory (Cesàro limits, renewal equation)")
TAGS = ["bitcoin", "selfish-mining", "markov-chain", "ergodic", "cesaro", "renewal", "long-run-average", "formal-verification", "mathlib"]

DEFINITION = {
    "definition_name": "BitcoinSelfishErgodic",
    "definition_title": "Distributions of the selfish-mining chain over time, Cesàro averages, and time-averaged revenues",
    "natural_language_statement": r"""Names over the selfish-mining missions' chain (`State`, `P`, `stateSum`, `poolExpGain`, `othersExpGain`).

**`delta t`** — the point mass at state $t$. **`dist α γ μ`** — one step of the chain on a distribution: $(\mathrm{dist}\,\mu)(s) = \sum_t \mu(t)\, P(t, s)$ through `stateSum`. **`distN α γ μ n`** — $n$ steps. **`IsDist μ`** — nonnegative, summable on the leads, total mass 1. **`cesaro α γ μ n`** — the average $\frac1n \sum_{k<n} \mathrm{distN}\,\mu\,k$ (the expected fraction of the first $n$ times spent in each state).

**`expPoolGain α γ μ`**, **`expOthersGain α γ μ`** — expected blocks credited per step when the state has distribution $\mu$. **`avgPoolGain α γ n`**, **`avgOthersGain α γ n`** — expected blocks per step over the first $n$ steps from `zero`; **`avgRelativeRevenue α γ n`** — their ratio, the pool's time-averaged revenue share (real division, 0 when the denominator is 0).

**`kill μ`** — the distribution with the mass at `zero` removed. **`taboo α γ t n`** — the sub-distribution of the chain from $t$ killed on hitting `zero` at times $\ge 1$. **`firstPassage α γ t n`** — the probability of first hitting `zero` at time $n+1$ from $t$. **`returnProb α γ n`** — $P(X_n = \text{zero} \mid X_0 = \text{zero})$. **`noPassage α γ t n`** — the probability of not having hit `zero` by time $n$.

**Formalization Note.** Imports Mathlib and the two selfish-mining missions' definitions. Real division by zero is 0.""",
}

T = {}
T["dist_zero"] = ("One step into zero", r"""`dist α γ μ zero = (1-α)μ(zero) + μ(tie) + (1-α)μ(lead 1)`.""")
T["dist_tie"] = ("One step into the tie", r"""`dist α γ μ tie = (1-α)μ(lead 0)`.""")
T["dist_lead_zero"] = ("One step into a lead of 1", r"""`dist α γ μ (lead 0) = α μ(zero)`.""")
T["dist_lead_one"] = ("One step into a lead of 2", r"""`dist α γ μ (lead 1) = α μ(lead 0) + (1-α) μ(lead 2)`.""")
T["dist_lead_succ"] = ("One step into a lead of n+3", r"""`dist α γ μ (lead (n+2)) = α μ(lead (n+1)) + (1-α) μ(lead (n+3))`.""")
T["dist_mass"] = ("A step preserves total mass", r"""For μ summable on the leads, `stateSum (dist α γ μ) = stateSum μ`.""")
T["dist_summable_lead"] = ("A step preserves lead-summability", r"""If μ is summable on the leads, so is `dist α γ μ`.""")
T["dist_nonneg"] = ("A step preserves nonnegativity", r"""For $0 \le \alpha \le 1$ and nonnegative μ, `dist α γ μ` is nonnegative.""")
T["isDist_dist"] = ("A step maps distributions to distributions", r"""For $0 < \alpha < 1/2$, `IsDist μ` implies `IsDist (dist α γ μ)`.""")
T["isDist_distN"] = ("n steps map distributions to distributions", r"""`IsDist μ` implies `IsDist (distN α γ μ n)` for every $n$.""")
T["dist_stationary"] = ("The stationary distribution is a fixed point of one step", r"""`dist α γ (stationary α) = stationary α` for $0 < \alpha < 1/2$.""")
T["distN_stationary"] = ("The stationary distribution is a fixed point of n steps", r"""`distN α γ (stationary α) n = stationary α`.""")
T["isDist_delta"] = ("Point masses are distributions", r"""`IsDist (delta t)`.""")
T["le_one_of_isDist"] = ("A distribution is at most 1 everywhere", r"""`IsDist μ` implies $\mu(s) \le 1$.""")
T["distN_zero_lead_le"] = ("Geometric tails from zero", r"""From `zero`, the probability of a lead of $m+1$ after any number of steps is at most $(\alpha/(1-\alpha))^m$.""")
T["distN_delta_lead_le"] = ("Uniform geometric tails from any start", r"""From any point mass there is $C \ge 1$ with `distN … n (lead m) ≤ C (α/(1-α))^m` for all $n$, $m$: the family of distributions over time is tight.""")
T["cesaro_delta_tendsto"] = ("Cesàro convergence from any state", r"""For $0 < \alpha < 1/2$, any $\gamma$ and any start $t$: for every state $s$, `cesaro α γ (delta t) n s → stationary α s`. Tightness gives limit points; each is invariant with mass 1, hence the stationary distribution by the uniqueness mission.""")
T["cesaro_zero_tendsto"] = ("Cesàro convergence from zero", r"""The case $t = \text{zero}$.""")
T["distN_mix"] = ("n-step distributions are mixtures of point-mass runs", r"""For a distribution μ: `distN α γ μ n s = stateSum (fun t => μ t · distN α γ (delta t) n s)`.""")
T["cesaro_tendsto"] = ("Cesàro convergence from any initial distribution", r"""For any `IsDist μ` and every state $s$: `cesaro α γ μ n s → stationary α s`. The time-averaged occupation of every state converges to the paper's stationary distribution, from any start.""")
T["avgPoolGain_eq"] = ("The time-averaged pool gain is the expected gain under the Cesàro average", r"""`avgPoolGain α γ n = expPoolGain α γ (cesaro α γ (delta zero) n)`.""")
T["avgOthersGain_eq"] = ("The time-averaged honest gain is the expected gain under the Cesàro average", r"""As above for the honest miners.""")
T["avgPoolGain_tendsto"] = ("The pool's time-averaged revenue converges to the paper's rate", r"""`avgPoolGain α γ n → poolRevenue α γ`.""")
T["avgOthersGain_tendsto"] = ("The honest time-averaged revenue converges to the paper's rate", r"""`avgOthersGain α γ n → othersRevenue α γ`.""")
T["avgRelativeRevenue_tendsto"] = ("The pool's long-run revenue share is the paper's relative revenue", r"""For $0 < \alpha < 1/2$ and $0 \le \gamma \le 1$: `avgRelativeRevenue α γ n → relativeRevenue α γ`. Eyal and Sirer's formula is the long-run share of a pool that starts with no lead, not only a stationary quantity.""")
T["avgRelativeRevenue_eventually_gt"] = ("Above the threshold, the pool's realized share eventually exceeds its hashrate", r"""For $0 < \alpha < 1/2$, $0 \le \gamma \le 1$ and $\alpha > (1-\gamma)/(3-2\gamma)$: for all large $n$, $\alpha <$ `avgRelativeRevenue α γ n`. The threshold theorem as a statement about time.""")
T["firstReturn_zero"] = ("The first return to zero at time 1 has probability 1−α", r"""`firstPassage α γ zero 0 = 1 - α`: the return-time distribution charges time 1, so the renewal sequence is aperiodic.""")
T["last_exit"] = ("Last-exit decomposition", r"""`distN α γ (delta zero) n s = Σ_{k≤n} returnProb α γ k · taboo α γ zero (n-k) s`.""")
T["renewal_equation"] = ("The renewal equation for returns to zero", r"""`returnProb α γ (n+1) = Σ_{k≤n} firstPassage α γ zero k · returnProb α γ (n-k)`.""")
THEOREMS = {f"BitcoinSelfishErgodic.{k}": dict(title=v[0], nl=v[1], ms=None) for k, v in T.items()}
THEOREMS["BitcoinSelfishErgodic.cesaro_tendsto"]["ms"] = ("Cesàro convergence", "Tightness from geometric tails, limit points invariant with mass 1, uniqueness.")
ORDER = ["BitcoinSelfishErgodic." + k for k in ["dist_zero", "dist_tie", "dist_lead_zero", "dist_lead_one", "dist_lead_succ", "dist_mass",
  "dist_summable_lead", "dist_nonneg", "isDist_dist", "isDist_distN", "dist_stationary", "distN_stationary", "isDist_delta", "le_one_of_isDist",
  "distN_zero_lead_le", "distN_delta_lead_le", "cesaro_delta_tendsto", "cesaro_zero_tendsto", "distN_mix", "cesaro_tendsto",
  "avgPoolGain_eq", "avgOthersGain_eq", "avgPoolGain_tendsto", "avgOthersGain_tendsto", "avgRelativeRevenue_tendsto",
  "avgRelativeRevenue_eventually_gt", "firstReturn_zero", "last_exit", "renewal_equation"]]
