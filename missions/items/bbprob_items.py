SRC = ("J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): "
       "https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; "
       "the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)")
TAGS = ["bitcoin", "nakamoto-consensus", "backbone", "probability", "hoeffding", "honest-majority", "typical-execution", "formal-verification", "mathlib"]

DEFINITION = {
    "definition_name": "BitcoinBackboneProb",
    "definition_title": "The random mining process of the synchronous backbone model, and typicality on a horizon",
    "natural_language_statement": r"""The probabilistic layer under the backbone mission's `BitcoinBackbone`, over Mathlib's measure theory.

**`ber p`** — the Bernoulli($p$) measure on `Bool`. **`Round n t`** — one round's outcomes: one success bit per honest party ($n$ of them) and per adversarial query ($t$ of them); **`roundMeasure n t p`** — the product of independent Bernoulli($p$) bits. **`Trace n t`** — a sequence of rounds; **`P n t p`** — the product measure over all rounds (`Measure.infinitePi`).

**`honestCount`**, **`advCount`** — the numbers of successful honest parties and adversarial queries in a round; **`roundX`** ($1$ iff some honest success), **`roundY`** ($1$ iff exactly one honest success), **`roundW`** ($Z - Y$); **`X ω r`**, **`Y ω r`**, **`Z ω r`**, **`W ω r`** — the same for round $r$ of a trace. **`margin n t p`** $= n p (1-p)^{n-1} - t p$ ($E[Y] - E[Z]$); **`rate n t p`** $= \text{margin}^2 / (2 (t+1)^2)$.

**`TypicalOn ω lam L`** — the backbone mission's typicality inequality $\sum_{[a,b]} Z < \sum_{(a,b)} Y$ for every window with $a + \lambda \le b \le L$. **`toExecution ω L base advParent`** — the backbone `Execution` induced by a trace on the horizon $[1, L]$ for any network behaviour `base` and adversarial chain choices `advParent`: honest party $q$ mines in round $r \le L$ iff its bit is set; the adversary finds `Z ω r` blocks; after $L$ the execution is frozen (party 0 mines alone, the adversary finds nothing). **`TypicalTrunc ω lam L`** — the induced execution is typical in the backbone mission's sense.

**Formalization Note.** Imports Mathlib and the backbone mission. The adversary is modelled by its query count per round; its strategy (which chains it extends, what it delivers) is the arbitrary `advParent`/`base`, quantified universally in the end-to-end theorems.""",
}

T = {}
T["iIndepFun_rounds"] = ("The rounds of a trace are independent", r"""Under `P n t p` the round maps $\omega \mapsto \omega_r$ are mutually independent.""")
T["map_eval_P"] = ("Each round has the round law", r"""The image of `P n t p` under $\omega \mapsto \omega_r$ is `roundMeasure n t p`.""")
T["integral_roundY"] = ("Expected uniquely successful rounds", r"""$\int$ `roundY` $d(\text{roundMeasure}) = n p (1-p)^{n-1}$.""")
T["integral_roundX"] = ("Expected successful rounds", r"""$\int$ `roundX` $= 1 - (1-p)^n$.""")
T["integral_advCount"] = ("Expected adversarial blocks per round", r"""$\int$ `advCount` $= t p$.""")
T["expect_Y"] = ("E[Y_r] = n p (1-p)^(n-1)", r"""For every round $r$: $E[Y_r] = n p (1-p)^{n-1}$.""")
T["expect_X"] = ("E[X_r] = 1 - (1-p)^n", r"""For every round $r$.""")
T["expect_Z"] = ("E[Z_r] = t p", r"""For every round $r$.""")
T["expect_Y_sub_expect_Z"] = ("E[Y] − E[Z] is the margin", r"""$E[Y_r] - E[Z_r] =$ `margin n t p`.""")
T["margin_ge_of_honest_majority"] = ("Honest majority gives a positive margin", r"""If $t \le (1-\delta) n$ and $n p \le \delta/2$: `margin n t p` $\ge \delta p n / 2$.""")
T["expect_Z_add_le_expect_Y"] = ("Honest majority: E[Z] + δpn/2 ≤ E[Y]", r"""Under the same conditions, for every round.""")
T["expect_Z_lt_expect_Y"] = ("Honest majority: adversarial blocks are strictly fewer than uniquely successful rounds in expectation", r"""With $\delta, n, p > 0$ added: $E[Z_r] < E[Y_r]$.""")
T["sets_hoeffding"] = ("Hoeffding's inequality for the adversary's lead on finite sets of rounds", r"""For finite $T \subseteq S$ and $j \ge 0$ with $\varepsilon = j + |T| E[Y] - |S| E[Z] \ge 0$: $P(\sum_T Y + j \le \sum_S Z) \le \exp(-2\varepsilon^2 / (|S|(t+1)^2))$.""")
T["window_bound"] = ("A window fails typicality with exponentially small probability", r"""For a window $[a, a+k]$ with $k \ge 1$ and $2tp \le (k-1)\,\text{margin}$: $P(\sum_{(a,a+k)} Y \le \sum_{[a,a+k]} Z) \le \exp(-2((k-1)\text{margin} - 2tp)^2 / ((k+1)(t+1)^2))$.""")
T["window_bound_rate"] = ("Window failure in rate form", r"""If margin $> 0$ and $4tp \le (k-3)$ margin: the window fails with probability at most $\exp(-\text{rate}\cdot(k+1))$.""")
T["typicalOn_failure_le_of_window"] = ("Union bound over windows", r"""If every window of length at least $\lambda \ge 1$ fails with probability at most $\beta$, then $P(\neg$`TypicalOn ω lam L`$) \le L^2 \beta$.""")
T["typicalOn_failure_le"] = ("Typicality on a horizon fails with probability at most L² e^(−rate(λ+1))", r"""Under the window hypothesis at $\lambda$.""")
T["typicalOn_prob_ge"] = ("Typicality on a horizon holds with probability at least 1 − L² e^(−rate(λ+1))", r"""The complement of `typicalOn_failure_le`.""")
T["typical_toExecution_iff"] = ("Typicality of the induced execution does not depend on the network or the adversary's chain choices", r"""`(toExecution ω L base advParent).Typical lam ↔ TypicalTrunc ω lam L`.""")
T["typicalTrunc_failure_le"] = ("The induced execution is typical except with probability (L+1)² e^(−rate(λ+1))", r"""For $\lambda \ge 2$, margin $> 0$ and $4tp \le (\lambda-3)$ margin: $P(\neg$`TypicalTrunc`$) \le (L+1)^2 e^{-\text{rate}(\lambda+1)}$, covering every window including those crossing the horizon.""")
T["backbone_failure_le"] = ("Any deterministic consequence of typicality fails with probability at most (L+1)² e^(−rate(λ+1))", r"""For any property $Q$ of executions that holds for every legal typical execution (`hdet`): the probability that some network behaviour and adversarial chain choices produce a legal induced execution violating $Q$ is at most $(L+1)^2 e^{-\text{rate}(\lambda+1)}$.""")
T["backbone_prob_ge"] = ("With probability at least 1 − (L+1)² e^(−rate(λ+1)), every legal induced execution has every typicality consequence", r"""For any $Q$ with `hdet`: with probability at least $1 - (L+1)^2 e^{-\text{rate}(\lambda+1)}$, for all `base` and `advParent` (an adaptive adversary), a legal induced execution satisfies $Q$. With $Q$ the backbone mission's common prefix, chain growth or chain quality, this is the paper's Theorem: the properties hold except with probability exponentially small in $\lambda$, under honest majority.""")
THEOREMS = {f"BitcoinBackboneProb.{k}": dict(title=v[0], nl=v[1], ms=None) for k, v in T.items()}
THEOREMS["BitcoinBackboneProb.sets_hoeffding"]["ms"] = ("Concentration", "Hoeffding's inequality for the independent per-round differences, from Mathlib's sub-Gaussian bounds.")
THEOREMS["BitcoinBackboneProb.typicalTrunc_failure_le"]["ms"] = ("Union bound", "Windows inside the horizon by `window_bound_rate`, windows crossing it by the frozen tail.")
ORDER = ["BitcoinBackboneProb." + k for k in ["iIndepFun_rounds", "map_eval_P", "integral_roundY", "integral_roundX", "integral_advCount",
  "expect_Y", "expect_X", "expect_Z", "expect_Y_sub_expect_Z", "margin_ge_of_honest_majority", "expect_Z_add_le_expect_Y", "expect_Z_lt_expect_Y",
  "sets_hoeffding", "window_bound", "window_bound_rate", "typicalOn_failure_le_of_window", "typicalOn_failure_le", "typicalOn_prob_ge",
  "typical_toExecution_iff", "typicalTrunc_failure_le", "backbone_failure_le", "backbone_prob_ge"]]
