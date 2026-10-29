# Read-back: `BitcoinSelfishErgodic.avgRelativeRevenue_tendsto`

**Setting.** $\alpha, \gamma$ are real numbers with $0 < \alpha < \tfrac12$ and $0 \le \gamma \le 1$.

**Assertion.** The real sequence $(R_n)_{n\in\mathbb{N}}$ of time-averaged relative revenues converges, as $n\to\infty$, to the stationary relative revenue:
$$\lim_{n\to\infty} \frac{A_n}{A_n + B_n} = \mathrm{Rel}(\alpha,\gamma) = \frac{\mathrm{Rev}^{\mathrm{pool}}(\alpha,\gamma)}{\mathrm{Rev}^{\mathrm{pool}}(\alpha,\gamma)+\mathrm{Rev}^{\mathrm{oth}}(\alpha,\gamma)},$$
where both fractions use the convention "division by $0$ gives $0$".

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

**Per-step credits.** Blocks credited at a transition from state $s$ under outcome $o$ (natural numbers, cast to reals):

| current state | pool credit (pool / hP / hO) | others credit (pool / hP / hO) |
|---|---|---|
| $\mathsf{zero}$ | $0 \,/\, 0 \,/\, 0$ | $0 \,/\, 1 \,/\, 1$ |
| $\mathsf{tie}$ | $2 \,/\, 1 \,/\, 0$ | $0 \,/\, 1 \,/\, 2$ |
| $\mathsf{lead}_0$ | $0 \,/\, 0 \,/\, 0$ | $0 \,/\, 0 \,/\, 0$ |
| $\mathsf{lead}_1$ | $0 \,/\, 2 \,/\, 2$ | $0 \,/\, 0 \,/\, 0$ |
| $\mathsf{lead}_{m+2}$ ($m\ge0$) | $0 \,/\, 1 \,/\, 1$ | $0 \,/\, 0 \,/\, 0$ |

The expected per-step credits are the weight-averages $g_{\alpha,\gamma}(s) = \sum_o q_o \cdot(\text{pool credit})$ and $h_{\alpha,\gamma}(s) = \sum_o q_o \cdot(\text{others credit})$ with the (possibly negative, if $\alpha,\gamma$ are out of range) weights $q_o$ above. Explicitly, for all real $\alpha,\gamma$:
$$\begin{aligned}
&g(\mathsf{zero}) = 0,\quad g(\mathsf{tie}) = 2\alpha + (1-\alpha)\gamma,\quad g(\mathsf{lead}_0) = 0,\quad g(\mathsf{lead}_1) = 2(1-\alpha),\quad g(\mathsf{lead}_{m+2}) = 1-\alpha;\\
&h(\mathsf{zero}) = 1-\alpha,\quad h(\mathsf{tie}) = (1-\alpha)(2-\gamma),\quad h(\mathsf{lead}_m) = 0 \text{ for all } m.
\end{aligned}$$

**Time-averaged credits from $\mathsf{zero}$.** For $n \in \mathbb{N}$,
$$A_n = \frac{1}{n}\sum_{k=0}^{n-1}\Sigma\big(s \mapsto (D^k\delta_{\mathsf{zero}})(s)\, g(s)\big), \qquad B_n = \frac{1}{n}\sum_{k=0}^{n-1}\Sigma\big(s \mapsto (D^k\delta_{\mathsf{zero}})(s)\, h(s)\big),$$
with $1/0 = 0$, so $A_0 = B_0 = 0$. Each inner $\Sigma$ uses the "series is $0$ if not summable" convention separately for each $k$. Since $h$ vanishes on the lead states, $B_n = \frac1n\sum_{k<n}\big[(1-\alpha)(D^k\delta_{\mathsf{zero}})(\mathsf{zero}) + (1-\alpha)(2-\gamma)(D^k\delta_{\mathsf{zero}})(\mathsf{tie})\big]$.

**Time-averaged relative revenue.** $R_n = \dfrac{A_n}{A_n + B_n}$, where real division by $0$ gives $0$: $R_n = 0$ whenever $A_n + B_n = 0$, in particular $R_0 = 0$.

**The fixed distribution $\pi_\alpha$** (it depends on $\alpha$ only). With $d(\alpha) = 2\alpha^3 - 4\alpha^2 + 1$,
$$\pi_\alpha(\mathsf{zero}) = \frac{1-2\alpha}{d(\alpha)}, \qquad \pi_\alpha(\mathsf{tie}) = \frac{(1-\alpha)(\alpha - 2\alpha^2)}{d(\alpha)}, \qquad \pi_\alpha(\mathsf{lead}_m) = \Big(\frac{\alpha}{1-\alpha}\Big)^{m}\cdot\frac{\alpha - 2\alpha^2}{d(\alpha)},$$
with real division by $0$ giving $0$. (For $0 < \alpha < \tfrac12$ one has $\tfrac14 < d(\alpha) < 1$ and $0 < \alpha/(1-\alpha) < 1$, so no division by zero occurs there.)

**Stationary revenues.**
$$\mathrm{Rev}^{\mathrm{pool}}(\alpha,\gamma) = \Sigma\big(s \mapsto \pi_\alpha(s)\,g(s)\big) = \pi_\alpha(\mathsf{tie})\big(2\alpha + (1-\alpha)\gamma\big) + \sum_{m \ge 0}\pi_\alpha(\mathsf{lead}_m)\,g(\mathsf{lead}_m)$$
(series set to $0$ if not summable; its terms are $0$ for $m=0$, $2(1-\alpha)\pi_\alpha(\mathsf{lead}_1)$ for $m=1$, $(1-\alpha)\pi_\alpha(\mathsf{lead}_m)$ for $m \ge 2$), and
$$\mathrm{Rev}^{\mathrm{oth}}(\alpha,\gamma) = \Sigma\big(s \mapsto \pi_\alpha(s)\,h(s)\big) = (1-\alpha)\,\pi_\alpha(\mathsf{zero}) + (1-\alpha)(2-\gamma)\,\pi_\alpha(\mathsf{tie}).$$

**Stationary relative revenue.** $\mathrm{Rel}(\alpha,\gamma) = \dfrac{\mathrm{Rev}^{\mathrm{pool}}(\alpha,\gamma)}{\mathrm{Rev}^{\mathrm{pool}}(\alpha,\gamma) + \mathrm{Rev}^{\mathrm{oth}}(\alpha,\gamma)}$, which is $0$ if the denominator is $0$.
