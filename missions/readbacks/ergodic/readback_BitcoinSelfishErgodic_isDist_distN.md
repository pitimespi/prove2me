# Read-back: `BitcoinSelfishErgodic.isDist_distN`

**Setting.** $\alpha, \gamma$ are real numbers with $0 < \alpha < \tfrac12$; there is **no hypothesis on $\gamma$** (it may be any real number, e.g. negative or larger than $1$). Also $\mu : S \to \mathbb{R}$ is assumed to be a distribution, and $n$ is an arbitrary natural number.

**Assertion.** $D^n\mu$ is a distribution: $(D^n\mu)(s) \ge 0$ for all states $s$, the sequence $\big((D^n\mu)(\mathsf{lead}_m)\big)_{m\ge0}$ is summable, and $\Sigma(D^n\mu) = 1$.

---

## Definitions used, unfolded

**State space $S$.** The states are $\mathsf{zero}$, $\mathsf{tie}$, and one state $\mathsf{lead}_m$ for every natural number $m = 0, 1, 2, \dots$; all of these are distinct. (The source comments say that $\mathsf{lead}_m$ stands for a private lead of $m+1$ blocks, so $\mathsf{lead}_0$ is "lead 1", $\mathsf{lead}_1$ is "lead 2", and so on. Formally these are only labels, and every subscript below is this shifted index.)

**Sum over all states.** For any $f : S \to \mathbb{R}$,
$$\Sigma f \;=\; f(\mathsf{zero}) + f(\mathsf{tie}) + \sum_{m \ge 0} f(\mathsf{lead}_m),$$
where the infinite series is the value of the series when the real sequence $\big(f(\mathsf{lead}_m)\big)_{m \ge 0}$ is summable (for real sequences: absolutely summable). The series is **defined to be $0$** when that sequence is not summable.

**One-step transition weights $P_{\alpha,\gamma}$.** For arbitrary real numbers $\alpha, \gamma$ (the definitions themselves impose no range), there are three outcomes, with weights
$$q_{\mathrm{pool}} = \alpha, \qquad q_{\mathrm{hP}} = (1-\alpha)\gamma, \qquad q_{\mathrm{hO}} = (1-\alpha)(1-\gamma).$$
A deterministic successor map $\mathrm{step}(s, o)$ is given by

| current state | outcome pool | outcome hP | outcome hO |
|---|---|---|---|
| $\mathsf{zero}$ | $\mathsf{lead}_0$ | $\mathsf{zero}$ | $\mathsf{zero}$ |
| $\mathsf{tie}$ | $\mathsf{zero}$ | $\mathsf{zero}$ | $\mathsf{zero}$ |
| $\mathsf{lead}_0$ | $\mathsf{lead}_1$ | $\mathsf{tie}$ | $\mathsf{tie}$ |
| $\mathsf{lead}_1$ | $\mathsf{lead}_2$ | $\mathsf{zero}$ | $\mathsf{zero}$ |
| $\mathsf{lead}_{m+2}$ ($m \ge 0$) | $\mathsf{lead}_{m+3}$ | $\mathsf{lead}_{m+1}$ | $\mathsf{lead}_{m+1}$ |

and $P_{\alpha,\gamma}(s, t) = \sum_{o \,:\, \mathrm{step}(s,o) = t} q_o$ (sum of the weights of the outcomes leading from $s$ to $t$). Using $q_{\mathrm{hP}} + q_{\mathrm{hO}} = 1-\alpha$ and $q_{\mathrm{pool}} + q_{\mathrm{hP}} + q_{\mathrm{hO}} = 1$, the only entries that can be nonzero are
$$\begin{aligned}
&P(\mathsf{zero},\mathsf{lead}_0) = \alpha, && P(\mathsf{zero},\mathsf{zero}) = 1-\alpha, && P(\mathsf{tie},\mathsf{zero}) = 1,\\
&P(\mathsf{lead}_0,\mathsf{lead}_1) = \alpha, && P(\mathsf{lead}_0,\mathsf{tie}) = 1-\alpha, && \\
&P(\mathsf{lead}_1,\mathsf{lead}_2) = \alpha, && P(\mathsf{lead}_1,\mathsf{zero}) = 1-\alpha, && \\
&P(\mathsf{lead}_{m+2},\mathsf{lead}_{m+3}) = \alpha, && P(\mathsf{lead}_{m+2},\mathsf{lead}_{m+1}) = 1-\alpha \quad (m \ge 0), &&
\end{aligned}$$
and every other entry is $0$. These identities hold for every real $\alpha, \gamma$: the transition weights do not depend on $\gamma$, each row sums to $1$, and all entries are $\ge 0$ exactly when $0 \le \alpha \le 1$.

**Point mass.** For a state $t$, $\delta_t(s) = 1$ if $s = t$ and $\delta_t(s) = 0$ otherwise.

**One step applied to a function.** For any $\mu : S \to \mathbb{R}$ (not required to be nonnegative, summable or normalized),
$$(D\mu)(s) \;=\; \Sigma\big(t \mapsto \mu(t)\, P_{\alpha,\gamma}(t, s)\big) \;=\; \mu(\mathsf{zero})P(\mathsf{zero},s) + \mu(\mathsf{tie})P(\mathsf{tie},s) + \sum_{m\ge 0}\mu(\mathsf{lead}_m)P(\mathsf{lead}_m,s).$$
(The parameters $\alpha,\gamma$ are implicit in $D = D_{\alpha,\gamma}$.) For a fixed target $s$, at most two lead states $t$ have $P(t,s) \ne 0$, so the lead series here has only finitely many nonzero terms and is an ordinary finite sum.

**$n$ steps.** $D^0\mu = \mu$ and $D^{n+1}\mu = D(D^n\mu)$ for $n \ge 0$.

**Probability distribution.** A function $\mu : S \to \mathbb{R}$ *is a distribution* exactly when all three hold: (i) $\mu(s) \ge 0$ for every state $s$; (ii) the sequence $\big(\mu(\mathsf{lead}_m)\big)_{m\ge0}$ is summable; (iii) $\Sigma\mu = 1$, i.e. $\mu(\mathsf{zero}) + \mu(\mathsf{tie}) + \sum_{m \ge 0}\mu(\mathsf{lead}_m) = 1$.
