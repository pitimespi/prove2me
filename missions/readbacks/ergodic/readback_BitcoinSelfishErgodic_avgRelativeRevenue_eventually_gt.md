# Read-back: `BitcoinSelfishErgodic.avgRelativeRevenue_eventually_gt`

**Setting.** $\alpha, \gamma$ are real numbers satisfying all of
$$0 < \alpha < \tfrac12, \qquad 0 \le \gamma \le 1, \qquad \alpha > \theta(\gamma) = \frac{1-\gamma}{3-2\gamma}.$$

**Assertion.** For all sufficiently large $n$ the time-averaged relative revenue strictly exceeds $\alpha$: there is $N \in \mathbb{N}$ such that for every $n \ge N$,
$$\alpha \;<\; R_n = \frac{A_n}{A_n + B_n}$$
(with $R_n = 0$ when $A_n + B_n = 0$). The statement is about the finite-$n$ quantities $R_n$ only; no limit appears in it.

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

**Threshold.** $\theta(\gamma) = \dfrac{1-\gamma}{3-2\gamma}$ (which would be $0$ at $\gamma = 3/2$ by the division-by-zero convention; for $0 \le \gamma \le 1$ the denominator lies in $[1,3]$).
