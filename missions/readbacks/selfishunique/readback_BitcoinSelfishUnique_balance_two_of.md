# Read-back: `Thm_BitcoinSelfishUnique_balance_two_of.lean`

**Theorem `BitcoinSelfishUnique.balance_two_of`.** For every real number $\alpha$, every real number $\gamma$, and every function $\pi$ from the state type to $\mathbb{R}$, under the single hypothesis $h : \mathrm{IsStationary}_{\alpha,\gamma}(\pi)$ (which bundles the four conditions nonneg, summable, mass and invariant spelled out below), the following equality of real numbers holds:
$$\pi(\ell_1) = \alpha\,\pi(\ell_0) + (1-\alpha)\,\pi(\ell_2).$$
Here $\ell_k$ is the state `lead k` (described in the definition file's documentation as a private lead of $k+1$ blocks, so the equation relates the states the documentation calls "lead $2$", "lead $1$" and "lead $3$"). The statement places **no** hypothesis on $\alpha$ or $\gamma$ beyond their being real numbers: no assumption $0<\alpha$, $\alpha<1/2$, or anything about $\gamma$. The conclusion is written with the literal coefficient $1-\alpha$, whereas the invariant condition at the state $\ell_1$ (see below) is written with the coefficient $h(\alpha,\gamma) = (1-\alpha)\gamma + (1-\alpha)(1-\gamma)$, the incoming weights to $\ell_1$ being $P_{\alpha,\gamma}(\ell_0,\ell_1) = \alpha$ and $P_{\alpha,\gamma}(\ell_2,\ell_1) = h(\alpha,\gamma)$; the two coefficients are equal as polynomials for all real $\alpha,\gamma$. The conclusion involves no division and no infinite sum. All four fields of $h$ are available as hypotheses; the statement itself does not indicate which of them (in particular whether nonneg, summable or mass) are needed.

### Setting and unfolded definitions (as they are actually defined in the bundle)

Throughout, $\alpha$ and $\gamma$ are real numbers. Unless a hypothesis is listed explicitly for the declaration below, nothing restricts them: they need not lie in $[0,1]$, so the "probabilities" below are simply real numbers that may be negative or exceed $1$.

**States.** The state type has exactly these elements: a state $0$ (the constructor `zero`), a state $0'$ (the constructor `tie`), and, for every natural number $n = 0, 1, 2, \dots$, a state $\ell_n$ (the constructor `lead n`). The documentation in the definition file says that $\ell_n$ encodes a private lead of $n+1$ blocks, so $\ell_0$ is "lead $1$", $\ell_1$ is "lead $2$", and $\ell_{n+2}$ is "lead $n+3$"; the code itself only ever works with the index $n$.

**Outcomes and their weights.** There are exactly three outcomes, $\mathrm{pool}$, $\mathrm{hP}$ (honest miner on the pool's branch) and $\mathrm{hO}$ (honest miner on the honest branch), with real weights
$$w_{\alpha,\gamma}(\mathrm{pool}) = \alpha,\qquad w_{\alpha,\gamma}(\mathrm{hP}) = (1-\alpha)\,\gamma,\qquad w_{\alpha,\gamma}(\mathrm{hO}) = (1-\alpha)(1-\gamma).$$
Write $h(\alpha,\gamma) := (1-\alpha)\gamma + (1-\alpha)(1-\gamma)$ for the sum of the two honest weights. As a polynomial identity, valid for all real $\alpha,\gamma$, one has $h(\alpha,\gamma) = 1-\alpha$ and $\alpha + h(\alpha,\gamma) = 1$; the definitions, however, are written with the unsimplified expressions.

**One-step map.** The function $\mathrm{step}(s,o)$ sends a state and an outcome to a state:
- $\mathrm{step}(0,\mathrm{pool}) = \ell_0$; $\mathrm{step}(0,\mathrm{hP}) = \mathrm{step}(0,\mathrm{hO}) = 0$;
- $\mathrm{step}(0',o) = 0$ for each of the three outcomes $o$;
- $\mathrm{step}(\ell_0,\mathrm{pool}) = \ell_1$; $\mathrm{step}(\ell_0,\mathrm{hP}) = \mathrm{step}(\ell_0,\mathrm{hO}) = 0'$;
- $\mathrm{step}(\ell_1,\mathrm{pool}) = \ell_2$; $\mathrm{step}(\ell_1,\mathrm{hP}) = \mathrm{step}(\ell_1,\mathrm{hO}) = 0$;
- for every $n \ge 0$: $\mathrm{step}(\ell_{n+2},\mathrm{pool}) = \ell_{n+3}$; $\mathrm{step}(\ell_{n+2},\mathrm{hP}) = \mathrm{step}(\ell_{n+2},\mathrm{hO}) = \ell_{n+1}$.

**Transition kernel.** For states $s,t$,
$$P_{\alpha,\gamma}(s,t) := \sum_{o \in \{\mathrm{pool},\,\mathrm{hP},\,\mathrm{hO}\}} \big[\mathrm{step}(s,o) = t\big]\; w_{\alpha,\gamma}(o),$$
where $[\,\cdot\,]$ is $1$ if the equality holds and $0$ otherwise (the three-term sum is taken in the order pool, hP, hO). Reading off the step map, the only entries that are not literally a sum of three zeros are:

| from $s$ | to $t$ | $P_{\alpha,\gamma}(s,t)$ |
|---|---|---|
| $0$ | $\ell_0$ | $\alpha$ |
| $0$ | $0$ | $h(\alpha,\gamma)$ |
| $0'$ | $0$ | $\alpha + h(\alpha,\gamma)$ |
| $\ell_0$ | $\ell_1$ | $\alpha$ |
| $\ell_0$ | $0'$ | $h(\alpha,\gamma)$ |
| $\ell_1$ | $\ell_2$ | $\alpha$ |
| $\ell_1$ | $0$ | $h(\alpha,\gamma)$ |
| $\ell_{n+2}$ ($n \ge 0$) | $\ell_{n+3}$ | $\alpha$ |
| $\ell_{n+2}$ ($n \ge 0$) | $\ell_{n+1}$ | $h(\alpha,\gamma)$ |

Every other pair $(s,t)$ has $P_{\alpha,\gamma}(s,t) = 0$.

**Sums over all states.** For a real-valued function $f$ on states,
$$\mathrm{stateSum}(f) := f(0) + f(0') + {\sum_{n=0}^{\infty}}' f(\ell_n),$$
where ${\sum}'$ is Mathlib's `tsum`: if the family $(f(\ell_n))_{n\in\mathbb{N}}$ is summable (unconditionally summable in $\mathbb{R}$, which for real numbers is the same as absolute convergence), it is the ordinary infinite sum; if the family is **not** summable, the tail is defined to be $0$. A family with only finitely many nonzero terms is summable and its `tsum` is the finite sum of those terms.

**The predicate "IsStationary".** For real $\alpha,\gamma$ and a function $\pi$ from states to $\mathbb{R}$, $\mathrm{IsStationary}_{\alpha,\gamma}(\pi)$ is the conjunction of the following four conditions (it is a structure with four fields; being given it as a hypothesis means all four are available, and the statement of a theorem does not say which of them its proof uses):

1. **nonneg**: for every state $s$, $0 \le \pi(s)$.
2. **summable**: the family $(\pi(\ell_n))_{n \in \mathbb{N}}$ is summable in $\mathbb{R}$.
3. **mass**: $\mathrm{stateSum}(\pi) = 1$, i.e. $\pi(0) + \pi(0') + {\sum}'_{n} \pi(\ell_n) = 1$. (Because of condition 2 the tail here is the genuine infinite sum, not the $0$ fallback.)
4. **invariant**: for every state $s$,
$$\pi(s) = \mathrm{stateSum}\big(t \mapsto \pi(t)\,P_{\alpha,\gamma}(t,s)\big) = \pi(0)P_{\alpha,\gamma}(0,s) + \pi(0')P_{\alpha,\gamma}(0',s) + {\sum_{n=0}^{\infty}}' \pi(\ell_n)\,P_{\alpha,\gamma}(\ell_n,s).$$
By the table above, for each fixed target $s$ the family $n \mapsto \pi(\ell_n)P_{\alpha,\gamma}(\ell_n,s)$ has at most one nonzero term, so this tail is always a genuine (finite) sum. Unfolding the table, condition 4 says exactly the following five families of equations, where $h = h(\alpha,\gamma) = (1-\alpha)\gamma + (1-\alpha)(1-\gamma)$:
   - at $s = 0$: $\pi(0) = h\,\pi(0) + (\alpha + h)\,\pi(0') + h\,\pi(\ell_1)$;
   - at $s = 0'$: $\pi(0') = h\,\pi(\ell_0)$;
   - at $s = \ell_0$: $\pi(\ell_0) = \alpha\,\pi(0)$;
   - at $s = \ell_1$: $\pi(\ell_1) = \alpha\,\pi(\ell_0) + h\,\pi(\ell_2)$;
   - at $s = \ell_{m+2}$ for every $m \ge 0$: $\pi(\ell_{m+2}) = \alpha\,\pi(\ell_{m+1}) + h\,\pi(\ell_{m+3})$.

   Note that the invariant condition does not mention $\gamma$ except through $h(\alpha,\gamma)$ and $\alpha + h(\alpha,\gamma)$, which simplify to $1-\alpha$ and $1$ for every real $\gamma$.
