# Read-back: `Def_BitcoinSelfishErgodic` (definition file)

This file imports the selfish-mining model file and the stationary-distribution file. The imported objects used below are unfolded in the section *Imported objects, unfolded* at the end. All parameters $\alpha, \gamma$ appearing below are arbitrary real numbers: **no definition in this file restricts $\alpha$ or $\gamma$**. The imported predicate "stationary distribution" (a function that is nonnegative, summable on the lead states, has $\Sigma = 1$ and satisfies $\mu(s) = \Sigma(t \mapsto \mu(t)P_{\alpha,\gamma}(t,s))$ for every $s$) is not used by any definition in this file.

## Declarations, in order

**1. Countability of the state space.** The file registers the fact that the state space $S$ is countable, witnessed by the injective map $\mathsf{zero} \mapsto 0$, $\mathsf{tie} \mapsto 1$, $\mathsf{lead}_m \mapsto m + 2$ into $\mathbb{N}$. This is a typeclass fact only; it does not define any number or function used elsewhere.

**2. Point mass $\delta_t$.** For a state $t$, $\delta_t : S \to \mathbb{R}$ is defined by $\delta_t(s) = 1$ if $s = t$ and $\delta_t(s) = 0$ otherwise.

**3. One step $D_{\alpha,\gamma}$.** For real $\alpha,\gamma$ and any $\mu : S \to \mathbb{R}$ (no sign, summability or normalization required), $D_{\alpha,\gamma}\mu : S \to \mathbb{R}$ is
$$(D_{\alpha,\gamma}\mu)(s) = \Sigma\big(t \mapsto \mu(t)\,P_{\alpha,\gamma}(t,s)\big) = \mu(\mathsf{zero})P(\mathsf{zero},s) + \mu(\mathsf{tie})P(\mathsf{tie},s) + \sum_{m\ge0}\mu(\mathsf{lead}_m)P(\mathsf{lead}_m,s),$$
with $\Sigma$ and $P$ as unfolded below. For a fixed target $s$ at most two lead states $t$ have $P(t,s)\neq 0$, so the lead series is a finite sum and the "$0$ if not summable" clause of $\Sigma$ never applies here.

**4. $n$ steps $D^n_{\alpha,\gamma}$.** Defined by recursion on $n \in \mathbb{N}$: $D^0\mu = \mu$ and $D^{n+1}\mu = D_{\alpha,\gamma}(D^n\mu)$.

**5. Distribution predicate.** A function $\mu : S \to \mathbb{R}$ *is a distribution* exactly when all three hold: (i) $\mu(s) \ge 0$ for every state $s$; (ii) the real sequence $\big(\mu(\mathsf{lead}_m)\big)_{m\ge0}$ is summable; (iii) $\Sigma\mu = \mu(\mathsf{zero}) + \mu(\mathsf{tie}) + \sum_{m\ge0}\mu(\mathsf{lead}_m) = 1$. It involves no $\alpha,\gamma$.

**6. Cesàro average $C_n$.** For real $\alpha,\gamma$, $\mu : S\to\mathbb{R}$, $n \in \mathbb{N}$ and a state $s$,
$$(C_n\mu)(s) = \frac{1}{n}\sum_{k=0}^{n-1}(D^k_{\alpha,\gamma}\mu)(s).$$
Real division by $0$ is $0$, and the sum is empty for $n=0$, so $C_0\mu$ is the zero function.

**7. Expected pool credit $E^{\mathrm{pool}}_{\alpha,\gamma}(\mu)$.** For $\mu : S\to\mathbb{R}$,
$$E^{\mathrm{pool}}(\mu) = \Sigma\big(s\mapsto\mu(s)\,g_{\alpha,\gamma}(s)\big) = \mu(\mathsf{tie})\big(2\alpha+(1-\alpha)\gamma\big) + \sum_{m\ge0}\mu(\mathsf{lead}_m)\,g(\mathsf{lead}_m),$$
where $g$ is the expected per-step pool credit (below; $g(\mathsf{zero}) = g(\mathsf{lead}_0) = 0$, $g(\mathsf{lead}_1) = 2(1-\alpha)$, $g(\mathsf{lead}_{m+2}) = 1-\alpha$), and the series is $0$ if not summable.

**8. Expected honest-miner credit $E^{\mathrm{oth}}_{\alpha,\gamma}(\mu)$.** For $\mu : S\to\mathbb{R}$,
$$E^{\mathrm{oth}}(\mu) = \Sigma\big(s\mapsto\mu(s)\,h_{\alpha,\gamma}(s)\big) = (1-\alpha)\,\mu(\mathsf{zero}) + (1-\alpha)(2-\gamma)\,\mu(\mathsf{tie}),$$
since $h$ vanishes on every lead state (so the lead series is the zero series).

**9. Time-averaged pool credit $A_n$.** For real $\alpha,\gamma$ and $n\in\mathbb{N}$,
$$A_n(\alpha,\gamma) = \frac1n\sum_{k=0}^{n-1}\Sigma\big(s\mapsto (D^k\delta_{\mathsf{zero}})(s)\,g(s)\big) = \frac1n\sum_{k=0}^{n-1}E^{\mathrm{pool}}\big(D^k\delta_{\mathsf{zero}}\big),$$
always starting from the point mass at $\mathsf{zero}$; each inner $\Sigma$ uses the "series is $0$ if not summable" convention separately, and $A_0 = 0$ (as $1/0 = 0$).

**10. Time-averaged honest-miner credit $B_n$.** For real $\alpha,\gamma$ and $n\in\mathbb{N}$,
$$B_n(\alpha,\gamma) = \frac1n\sum_{k=0}^{n-1}\Sigma\big(s\mapsto (D^k\delta_{\mathsf{zero}})(s)\,h(s)\big) = \frac1n\sum_{k=0}^{n-1}\Big[(1-\alpha)(D^k\delta_{\mathsf{zero}})(\mathsf{zero}) + (1-\alpha)(2-\gamma)(D^k\delta_{\mathsf{zero}})(\mathsf{tie})\Big],$$
with $B_0 = 0$.

**11. Time-averaged relative revenue $R_n$.** $R_n(\alpha,\gamma) = \dfrac{A_n}{A_n + B_n}$, where real division by $0$ gives $0$; so $R_n = 0$ whenever $A_n + B_n = 0$, and in particular $R_0 = 0$.

**12. Killing at $\mathsf{zero}$, $\kappa$.** For $\mu : S \to \mathbb{R}$, $(\kappa\mu)(s) = 0$ if $s = \mathsf{zero}$ and $(\kappa\mu)(s) = \mu(s)$ otherwise.

**13. Taboo functions $\tau^t_n$.** For real $\alpha,\gamma$ and a starting state $t$, defined by recursion on $n$: $\tau^t_0 = \delta_t$ (not killed; so $\tau^{\mathsf{zero}}_0 = \delta_{\mathsf{zero}}$ has value $1$ at $\mathsf{zero}$), and $\tau^t_{n+1} = \kappa\big(D_{\alpha,\gamma}\tau^t_n\big)$, i.e. one step followed by setting the value at $\mathsf{zero}$ to $0$.

**14. First passage $f^t_n$.** For real $\alpha,\gamma$, a state $t$ and $n\in\mathbb{N}$, $f^t_n = \big(D_{\alpha,\gamma}\tau^t_n\big)(\mathsf{zero})$: the value at $\mathsf{zero}$ after one step applied to the $n$-th taboo function (before killing). For example $f^t_0 = (D\delta_t)(\mathsf{zero}) = P_{\alpha,\gamma}(t,\mathsf{zero})$.

**15. Return sequence $r_n$.** For real $\alpha,\gamma$ and $n\in\mathbb{N}$, $r_n = \big(D^n_{\alpha,\gamma}\delta_{\mathsf{zero}}\big)(\mathsf{zero})$; in particular $r_0 = 1$.

**16. No-passage total $N^t_n$.** For real $\alpha,\gamma$, a state $t$ and $n\in\mathbb{N}$, $N^t_n = \Sigma\,\tau^t_n = \tau^t_n(\mathsf{zero}) + \tau^t_n(\mathsf{tie}) + \sum_{m\ge0}\tau^t_n(\mathsf{lead}_m)$, with the series set to $0$ if not summable. (For $n \ge 1$ the $\mathsf{zero}$ term is $0$ because of the killing; for $n = 0$ it is $\delta_t(\mathsf{zero})$.)

---

## Imported objects, unfolded

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
