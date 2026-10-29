# Read-back: `BitcoinSelfishErgodic.last_exit`

**Setting.** $\alpha, \gamma$ are arbitrary real numbers: there are **no hypotheses** on $\alpha$ or $\gamma$. Also $n$ is an arbitrary natural number and $s$ an arbitrary state.

**Assertion.**
$$\big(D^n\delta_{\mathsf{zero}}\big)(s) \;=\; \sum_{k=0}^{n} r_k\,\tau^{\mathsf{zero}}_{n-k}(s), \qquad r_k = \big(D^k\delta_{\mathsf{zero}}\big)(\mathsf{zero}).$$
Here $k$ ranges over $0,1,\dots,n$, so $n - k \ge 0$ and the natural-number subtraction is ordinary subtraction. The $k = n$ term is $r_n\,\tau^{\mathsf{zero}}_0(s) = r_n\,\delta_{\mathsf{zero}}(s)$.

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

**Killing at $\mathsf{zero}$.** $(\kappa\mu)(s) = 0$ if $s = \mathsf{zero}$, and $(\kappa\mu)(s) = \mu(s)$ otherwise.

**Taboo functions.** For a starting state $t$: $\tau^t_0 = \delta_t$ (not killed, so $\tau^{\mathsf{zero}}_0 = \delta_{\mathsf{zero}}$ has mass $1$ at $\mathsf{zero}$), and $\tau^t_{n+1} = \kappa\big(D\tau^t_n\big)$ for $n \ge 0$.

**First passage.** $f^t_n = \big(D\tau^t_n\big)(\mathsf{zero})$ for $n \ge 0$.

**Return sequence.** $r_n = \big(D^n\delta_{\mathsf{zero}}\big)(\mathsf{zero})$ for $n \ge 0$ (so $r_0 = 1$).
