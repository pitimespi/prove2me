# Read-back: `BitcoinSelfishErgodic.isDist_delta`

**Setting.** $t$ is an arbitrary state. No parameters $\alpha,\gamma$ are involved.

**Assertion.** The point mass $\delta_t$ is a distribution: $\delta_t(s) \ge 0$ for every $s$; the sequence $\big(\delta_t(\mathsf{lead}_m)\big)_{m\ge0}$ is summable; and $\Sigma\delta_t = \delta_t(\mathsf{zero}) + \delta_t(\mathsf{tie}) + \sum_{m\ge0}\delta_t(\mathsf{lead}_m) = 1$.

---

## Definitions used, unfolded

**State space $S$.** The states are $\mathsf{zero}$, $\mathsf{tie}$, and one state $\mathsf{lead}_m$ for every natural number $m = 0, 1, 2, \dots$; all of these are distinct. (The source comments say that $\mathsf{lead}_m$ stands for a private lead of $m+1$ blocks, so $\mathsf{lead}_0$ is "lead 1", $\mathsf{lead}_1$ is "lead 2", and so on. Formally these are only labels, and every subscript below is this shifted index.)

**Sum over all states.** For any $f : S \to \mathbb{R}$,
$$\Sigma f \;=\; f(\mathsf{zero}) + f(\mathsf{tie}) + \sum_{m \ge 0} f(\mathsf{lead}_m),$$
where the infinite series is the value of the series when the real sequence $\big(f(\mathsf{lead}_m)\big)_{m \ge 0}$ is summable (for real sequences: absolutely summable). The series is **defined to be $0$** when that sequence is not summable.

**Point mass.** For a state $t$, $\delta_t(s) = 1$ if $s = t$ and $\delta_t(s) = 0$ otherwise.

**Probability distribution.** A function $\mu : S \to \mathbb{R}$ *is a distribution* exactly when all three hold: (i) $\mu(s) \ge 0$ for every state $s$; (ii) the sequence $\big(\mu(\mathsf{lead}_m)\big)_{m\ge0}$ is summable; (iii) $\Sigma\mu = 1$, i.e. $\mu(\mathsf{zero}) + \mu(\mathsf{tie}) + \sum_{m \ge 0}\mu(\mathsf{lead}_m) = 1$.
