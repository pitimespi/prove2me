# Read-back: `Def_BitcoinSelfishMining.lean`

This file imports all of Mathlib and places every declaration below in the namespace `BitcoinSelfishMining`. Throughout, "real division by zero" follows Mathlib's convention $x/0 = 0$, and $\sum'$ denotes Mathlib's `tsum`, which equals the ordinary sum when the family is summable and equals $0$ when the family is not summable. The file's comments describe an intended interpretation (a selfish-mining pool, states labelled $0, 0', 1, 2, \dots$); the read-backs below record only what the code itself fixes, and mention the comments' labelling only where the task of unfolding the encoding requires it.

**`State`.** An inductive type with exactly three kinds of elements: a constant $\mathrm{zero}$, a constant $\mathrm{tie}$, and, for every natural number $n \in \mathbb{N} = \{0,1,2,\dots\}$, an element $\mathrm{lead}_n$. Distinct constructors and distinct indices give distinct states, so the type is countably infinite: $\{\mathrm{zero}, \mathrm{tie}\} \cup \{\mathrm{lead}_n : n \in \mathbb{N}\}$. The code attaches no numerical meaning to the index $n$; the file's comments say that $\mathrm{lead}_n$ is meant to represent a private lead of $n+1$ blocks (so that $\mathrm{lead}_0$, $\mathrm{lead}_1$, $\mathrm{lead}_{n+2}$ stand for the comments' "states" $1$, $2$, $n+3$), and that $\mathrm{tie}$ stands for the comments' state $0'$. Equality on `State` is decidable and the type can be printed.

**`Outcome`.** An inductive type with exactly three elements: $\mathrm{pool}$, $\mathrm{honestOnPool}$, $\mathrm{honestOnOthers}$. Equality is decidable.

**`outcomeProb`.** For real numbers $\alpha, \gamma \in \mathbb{R}$ (completely unconstrained: they need not lie in $[0,1]$), a real-valued function on `Outcome`:
$$
p_{\alpha,\gamma}(\mathrm{pool}) = \alpha,\qquad
p_{\alpha,\gamma}(\mathrm{honestOnPool}) = (1-\alpha)\gamma,\qquad
p_{\alpha,\gamma}(\mathrm{honestOnOthers}) = (1-\alpha)(1-\gamma).
$$
Nothing in the definition forces these three numbers to be non-negative or to sum to $1$ (though algebraically they always sum to $\alpha + (1-\alpha)\gamma + (1-\alpha)(1-\gamma)$, which simplifies to $1$ for every real $\alpha,\gamma$).

**`outcomeSum`.** For a real-valued function $f$ on `Outcome`, the real number
$$
\textstyle\sum_{o} f(o) \;:=\; f(\mathrm{pool}) + f(\mathrm{honestOnPool}) + f(\mathrm{honestOnOthers}).
$$
This is a plain three-term sum, with no weighting.

**`step`.** A function `State → Outcome → State` (a deterministic transition table), defined by cases, where "any other outcome" means either of the two outcomes $\mathrm{honestOnPool}$, $\mathrm{honestOnOthers}$:

- from $\mathrm{zero}$: on $\mathrm{pool}$ go to $\mathrm{lead}_0$; on any other outcome stay at $\mathrm{zero}$;
- from $\mathrm{tie}$: on every outcome (including $\mathrm{pool}$) go to $\mathrm{zero}$;
- from $\mathrm{lead}_0$: on $\mathrm{pool}$ go to $\mathrm{lead}_1$; on any other outcome go to $\mathrm{tie}$;
- from $\mathrm{lead}_1$: on $\mathrm{pool}$ go to $\mathrm{lead}_2$; on any other outcome go to $\mathrm{zero}$;
- from $\mathrm{lead}_{n+2}$ (i.e. $\mathrm{lead}_k$ with $k \ge 2$): on $\mathrm{pool}$ go to $\mathrm{lead}_{n+3}$ ($= \mathrm{lead}_{k+1}$); on any other outcome go to $\mathrm{lead}_{n+1}$ ($= \mathrm{lead}_{k-1}$).

In particular, in every state, $\mathrm{honestOnPool}$ and $\mathrm{honestOnOthers}$ lead to the same successor state; they are never distinguished by `step`.

**`poolGain`.** A function `State → Outcome → ℕ` (natural-number valued), defined by cases with a final catch-all:

- $(\mathrm{tie}, \mathrm{pool}) \mapsto 2$; $(\mathrm{tie}, \mathrm{honestOnPool}) \mapsto 1$; $(\mathrm{tie}, \mathrm{honestOnOthers}) \mapsto 0$;
- $(\mathrm{lead}_1, \mathrm{pool}) \mapsto 0$; $(\mathrm{lead}_1, \mathrm{honestOnPool}) \mapsto 2$; $(\mathrm{lead}_1, \mathrm{honestOnOthers}) \mapsto 2$;
- for every $m \in \mathbb{N}$: $(\mathrm{lead}_{m+2}, \mathrm{pool}) \mapsto 0$; $(\mathrm{lead}_{m+2}, \mathrm{honestOnPool}) \mapsto 1$; $(\mathrm{lead}_{m+2}, \mathrm{honestOnOthers}) \mapsto 1$;
- every remaining pair $\mapsto 0$; concretely, $(\mathrm{zero}, o) \mapsto 0$ and $(\mathrm{lead}_0, o) \mapsto 0$ for all three outcomes $o$.

**`othersGain`.** A function `State → Outcome → ℕ`, defined by cases with a final catch-all:

- $(\mathrm{zero}, \mathrm{pool}) \mapsto 0$; $(\mathrm{zero}, \mathrm{honestOnPool}) \mapsto 1$; $(\mathrm{zero}, \mathrm{honestOnOthers}) \mapsto 1$;
- $(\mathrm{tie}, \mathrm{honestOnPool}) \mapsto 1$; $(\mathrm{tie}, \mathrm{honestOnOthers}) \mapsto 2$;
- every remaining pair $\mapsto 0$; concretely, $(\mathrm{tie}, \mathrm{pool}) \mapsto 0$ and $(\mathrm{lead}_n, o) \mapsto 0$ for every $n \in \mathbb{N}$ and all three outcomes $o$.

**`P`.** For reals $\alpha, \gamma$ and states $s, t$, the real number
$$
P_{\alpha,\gamma}(s,t) \;:=\; \sum_{o \in \{\mathrm{pool},\,\mathrm{honestOnPool},\,\mathrm{honestOnOthers}\}} \big[\,\mathrm{step}(s,o) = t\,\big]\cdot p_{\alpha,\gamma}(o),
$$
where $[\cdot]$ is $1$ when the condition holds and $0$ otherwise, and $p_{\alpha,\gamma}$ is `outcomeProb`. Unfolding `step`, for each $s$ the only $t$ with a possibly non-zero value are: from $\mathrm{zero}$, $t=\mathrm{lead}_0$ with value $\alpha$ and $t=\mathrm{zero}$ with value $(1-\alpha)\gamma + (1-\alpha)(1-\gamma)$; from $\mathrm{tie}$, $t = \mathrm{zero}$ with value $\alpha + (1-\alpha)\gamma + (1-\alpha)(1-\gamma)$; from $\mathrm{lead}_0$, $t=\mathrm{lead}_1$ with value $\alpha$ and $t=\mathrm{tie}$ with value $(1-\alpha)\gamma + (1-\alpha)(1-\gamma)$; from $\mathrm{lead}_1$, $t = \mathrm{lead}_2$ with value $\alpha$ and $t = \mathrm{zero}$ with value $(1-\alpha)\gamma + (1-\alpha)(1-\gamma)$; from $\mathrm{lead}_{n+2}$, $t = \mathrm{lead}_{n+3}$ with value $\alpha$ and $t = \mathrm{lead}_{n+1}$ with value $(1-\alpha)\gamma + (1-\alpha)(1-\gamma)$. All other entries are $0$. No sign or normalisation constraint on $\alpha,\gamma$ is imposed.

**`poolExpGain`.** For reals $\alpha,\gamma$ and a state $s$, the real number
$$
g^{\mathrm{pool}}_{\alpha,\gamma}(s) \;:=\; \sum_{o} p_{\alpha,\gamma}(o)\cdot \mathrm{poolGain}(s,o),
$$
with the natural number $\mathrm{poolGain}(s,o)$ cast to a real. Unfolding: $g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{zero}) = 0$; $g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{tie}) = 2\alpha + (1-\alpha)\gamma\cdot 1 + (1-\alpha)(1-\gamma)\cdot 0$; $g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_0) = 0$; $g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_1) = \alpha\cdot 0 + (1-\alpha)\gamma\cdot 2 + (1-\alpha)(1-\gamma)\cdot 2$; $g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_{m+2}) = \alpha\cdot 0 + (1-\alpha)\gamma\cdot 1 + (1-\alpha)(1-\gamma)\cdot 1$.

**`othersExpGain`.** For reals $\alpha,\gamma$ and a state $s$, the real number
$$
g^{\mathrm{oth}}_{\alpha,\gamma}(s) \;:=\; \sum_{o} p_{\alpha,\gamma}(o)\cdot \mathrm{othersGain}(s,o).
$$
Unfolding: $g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{zero}) = \alpha\cdot 0 + (1-\alpha)\gamma\cdot 1 + (1-\alpha)(1-\gamma)\cdot 1$; $g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{tie}) = \alpha\cdot 0 + (1-\alpha)\gamma\cdot 1 + (1-\alpha)(1-\gamma)\cdot 2$; $g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{lead}_n) = 0$ for every $n$.

**`stateSum`.** For a real-valued function $f$ on `State`, the real number
$$
\Sigma_{\mathrm{State}}(f) \;:=\; f(\mathrm{zero}) + f(\mathrm{tie}) + \sum_{n=0}^{\infty}{}' f(\mathrm{lead}_n),
$$
where the last term is Mathlib's `tsum` over $n \in \mathbb{N}$: it is the value of the (unconditionally convergent) sum when the family $n \mapsto f(\mathrm{lead}_n)$ is summable, and it is $0$ when the family is not summable. No summability requirement is built into the definition, so $\Sigma_{\mathrm{State}}(f)$ is a well-defined real number for every $f$, possibly with a silently zeroed tail.

**`denom`.** For a real $\alpha$, the real polynomial value
$$
D(\alpha) \;:=\; 2\alpha^3 - 4\alpha^2 + 1 .
$$
No positivity or non-vanishing is asserted here.

**`stationary`.** For a real $\alpha$ (unconstrained), a real-valued function $\pi_\alpha$ on `State`:
$$
\pi_\alpha(\mathrm{zero}) = \frac{1-2\alpha}{D(\alpha)},\qquad
\pi_\alpha(\mathrm{tie}) = \frac{(1-\alpha)(\alpha - 2\alpha^2)}{D(\alpha)},\qquad
\pi_\alpha(\mathrm{lead}_n) = \left(\frac{\alpha}{1-\alpha}\right)^{n}\cdot\frac{\alpha - 2\alpha^2}{D(\alpha)}\quad (n\in\mathbb{N}),
$$
with $D(\alpha) = 2\alpha^3 - 4\alpha^2 + 1$. Division is real division with the convention $x/0 = 0$: if $D(\alpha) = 0$ then all three formulas give $0$; if $\alpha = 1$ then $\alpha/(1-\alpha) = 0$, so $\pi_1(\mathrm{lead}_0) = 1\cdot(\alpha-2\alpha^2)/D(\alpha)$ (since $0^0 = 1$) while $\pi_1(\mathrm{lead}_n) = 0$ for $n \ge 1$. The definition does not assert that these numbers are non-negative, sum to $1$, or are invariant under any transition; it is just this family of formulas. In terms of the comments' labelling, the comments' $p_k$ for $k\ge 1$ corresponds to $\pi_\alpha(\mathrm{lead}_{k-1})$.

**`poolRevenue`.** For reals $\alpha,\gamma$, the real number
$$
r^{\mathrm{pool}}_{\alpha,\gamma} \;:=\; \Sigma_{\mathrm{State}}\big(s \mapsto \pi_\alpha(s)\cdot g^{\mathrm{pool}}_{\alpha,\gamma}(s)\big)
= \pi_\alpha(\mathrm{zero})\,g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{zero}) + \pi_\alpha(\mathrm{tie})\,g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{tie}) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_n),
$$
where the tail is a `tsum` (equal to $0$ if the family $n \mapsto \pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{pool}}_{\alpha,\gamma}(\mathrm{lead}_n)$ is not summable). By the unfolding of `poolExpGain`, the $\mathrm{zero}$ term and the $n=0$ tail term are identically $0$.

**`othersRevenue`.** For reals $\alpha,\gamma$, the real number
$$
r^{\mathrm{oth}}_{\alpha,\gamma} \;:=\; \Sigma_{\mathrm{State}}\big(s \mapsto \pi_\alpha(s)\cdot g^{\mathrm{oth}}_{\alpha,\gamma}(s)\big)
= \pi_\alpha(\mathrm{zero})\,g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{zero}) + \pi_\alpha(\mathrm{tie})\,g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{tie}) + \sum_{n=0}^{\infty}{}'\,\pi_\alpha(\mathrm{lead}_n)\,g^{\mathrm{oth}}_{\alpha,\gamma}(\mathrm{lead}_n).
$$
By the unfolding of `othersExpGain`, every tail term is $0$, so the tail `tsum` is the sum of the zero family, i.e. $0$.

**`relativeRevenue`.** For reals $\alpha,\gamma$, the real number
$$
R_{\alpha,\gamma} \;:=\; \frac{r^{\mathrm{pool}}_{\alpha,\gamma}}{r^{\mathrm{pool}}_{\alpha,\gamma} + r^{\mathrm{oth}}_{\alpha,\gamma}},
$$
with the convention that the quotient is $0$ whenever $r^{\mathrm{pool}}_{\alpha,\gamma} + r^{\mathrm{oth}}_{\alpha,\gamma} = 0$.

**`closedForm`.** For reals $\alpha,\gamma$, the real number
$$
C(\alpha,\gamma) \;:=\; \frac{\alpha(1-\alpha)^2\big(4\alpha + \gamma(1-2\alpha)\big) - \alpha^3}{1 - \alpha\big(1 + (2-\alpha)\alpha\big)},
$$
whose denominator expands to $1 - \alpha - 2\alpha^2 + \alpha^3$; by the division convention, $C(\alpha,\gamma) = 0$ whenever that denominator vanishes. (Note that this denominator is a different polynomial from $D(\alpha) = 2\alpha^3 - 4\alpha^2 + 1$ used in `stationary`.)

**`profitThreshold`.** For a real $\gamma$, the real number
$$
\tau(\gamma) \;:=\; \frac{1-\gamma}{3-2\gamma},
$$
which by the division convention equals $0$ when $\gamma = 3/2$. No constraint on $\gamma$ is imposed by the definition.
