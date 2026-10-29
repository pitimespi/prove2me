# Read-back: `BitcoinBackboneProb.typicalOn_failure_le`

**Statement.** Let $n, t \in \mathbb N$, $p \in [0,1]$ and $\lambda, L \in \mathbb N$. Assume

- $\lambda \ge 1$;
- $m(n,t,p) > 0$;
- $4\,t\,p \le (\lambda - 3)\, m(n,t,p)$ (real arithmetic; $\lambda - 3$ may be negative).

Then
$$P_{n,t,p}\big(\{\omega : \text{not } \mathrm{TypOn}(\omega, \lambda, L)\}\big) \;\le\; L^2 \, \exp\!\big(-\kappa(n,t,p)\,(\lambda+1)\big),$$
with $L, \lambda$ cast to $\mathbb R$. The left side is the probability that some window $[a,b]$ with $a + \lambda \le b \le L$ violates $\sum_{[a,b]} Z < \sum_{(a,b)} Y$. For $L = 0$ the right side is $0$ (and, since $\lambda \ge 1$, no window exists, so $\mathrm{TypOn}$ holds for every $\omega$).

**Consequences of the hypotheses $m(n,t,p) > 0$ and $4tp \le (\lambda - 3)\,m(n,t,p)$** (stated because they restrict which parameter values the statement actually covers). Since $m = p\,\big(n(1-p)^{n \dot- 1} - t\big)$, the hypothesis $m > 0$ forces $p > 0$, $n \ge 1$ and $n(1-p)^{n\dot-1} > t$; for $n = 1$ this means $t = 0$ (any $p \in (0,1]$), for $n \ge 2$ it requires in particular $p < 1$. Since $4tp \ge 0$ and $m > 0$, the second hypothesis forces $\lambda \ge 3$, and when $\lambda = 3$ it forces $tp = 0$, i.e. $t = 0$. Thus values of $\lambda$ below $3$ that the stated lower bound on $\lambda$ admits make the hypotheses jointly unsatisfiable.
### Probabilistic round model (unfolded)

- **Parameters.** $n, t \in \mathbb N$ are arbitrary natural numbers (either may be $0$): $n$ is the number of honest parties, $t$ the number of adversarial queries per round. $p$ is an element of the closed unit interval $[0,1]$ (so $p = 0$ and $p = 1$ are allowed); wherever it appears in arithmetic it is the real number $p$. All casts of $n, t$ and other naturals into formulas are casts into $\mathbb R$ (so $(\lambda - 3)$, $(k-1)$ etc. below are real subtractions and may be negative), except where a natural-number subtraction is explicitly flagged.
- **Bernoulli law $\mathrm{ber}_p$.** The two-point Bernoulli measure on $\{\mathrm{true}, \mathrm{false}\}$ built by Mathlib's `bernoulliMeasure true false p`: mass $p$ on $\mathrm{true}$ and mass $1-p$ on $\mathrm{false}$. It is a probability measure.
- **Round outcomes $\mathcal R_{n,t}$.** A round outcome is a pair $\rho = (\rho_1, \rho_2)$ with $\rho_1 : \{0,\dots,n-1\} \to \{\mathrm{true},\mathrm{false}\}$ (which honest parties succeeded) and $\rho_2 : \{0,\dots,t-1\} \to \{\mathrm{true},\mathrm{false}\}$ (which adversarial queries succeeded). If $n = 0$ (resp. $t = 0$) the corresponding component is the unique empty function.
- **Round law $\mu_{n,t,p}$.** The product measure
$$\mu_{n,t,p} = \Big(\bigotimes_{i=0}^{n-1} \mathrm{ber}_p\Big) \otimes \Big(\bigotimes_{j=0}^{t-1} \mathrm{ber}_p\Big)$$
on $\mathcal R_{n,t}$ (product $\sigma$-algebra): all $n + t$ coordinates are independent, each $\mathrm{true}$ with probability $p$. It is a probability measure.
- **Traces $\Omega_{n,t}$.** A trace is an infinite sequence $\omega = (\omega_0, \omega_1, \omega_2, \dots)$ of round outcomes, indexed by **all** $r \in \mathbb N$ starting at $r = 0$; $\Omega_{n,t} = \mathcal R_{n,t}^{\mathbb N}$ with the product $\sigma$-algebra.
- **Trace law $P_{n,t,p}$.** The infinite product probability measure $P_{n,t,p} = \bigotimes_{r \in \mathbb N} \mu_{n,t,p}$ on $\Omega_{n,t}$ (Mathlib's `Measure.infinitePi`): the coordinates $\omega_r$ are i.i.d. with law $\mu_{n,t,p}$. It is a probability measure. For any set $A \subseteq \Omega_{n,t}$ (measurable or not; non-measurable sets get their outer measure), $P_{n,t,p}(A)$ below denotes the real number obtained by converting the (extended-nonnegative) measure of $A$ to $\mathbb R$; it lies in $[0,1]$.
- **Counts in one round.** For $\rho \in \mathcal R_{n,t}$:
$$\#_H(\rho) = \#\{\, i < n : \rho_1(i) = \mathrm{true} \,\} \in \{0,\dots,n\}, \qquad \#_A(\rho) = \#\{\, j < t : \rho_2(j) = \mathrm{true} \,\} \in \{0,\dots,t\}.$$
- **Round indicators.** $x(\rho) = 1$ if $\#_H(\rho) > 0$ and $0$ otherwise; $y(\rho) = 1$ if $\#_H(\rho) = 1$ and $0$ otherwise (both natural numbers); $w(\rho) = \#_A(\rho) - y(\rho)$ computed in $\mathbb R$.
- **Trace variables.** For $\omega \in \Omega_{n,t}$ and $r \in \mathbb N$ (including $r = 0$): $X_r(\omega) = x(\omega_r)$, $Y_r(\omega) = y(\omega_r)$, $Z_r(\omega) = \#_A(\omega_r)$ (natural numbers), $W_r(\omega) = w(\omega_r) \in \mathbb R$. So $X_r, Y_r \in \{0,1\}$ and $Z_r \in \{0,\dots,t\}$.
- **Margin.**
$$m(n,t,p) = n\,p\,(1-p)^{\,n \,\dot-\, 1} - t\,p \in \mathbb R,$$
where $n \dot- 1$ is natural-number subtraction (truncated at $0$): for $n = 0$ the exponent is $0$ and $m = -t p$; for $n = 1$, $m = p - tp$; the convention $0^0 = 1$ applies, so for $n = 1$, $p = 1$ the factor $(1-p)^0$ equals $1$.
- **Rate.**
$$\kappa(n,t,p) = \frac{m(n,t,p)^2}{2\,(t+1)^2} \ \ge 0$$
(the denominator is at least $2$, never zero).
### Window conventions

For natural numbers $a, b$: $[a,b] = \{a, a+1, \dots, b\}$ (closed window; empty if $a > b$, a single point if $a = b$) and $(a,b) = \{a+1, \dots, b-1\}$ (open window; empty whenever $b \le a + 1$). A sum over an empty index set is $0$. Sums of the natural-number variables $Y_i, Z_i$ are computed in $\mathbb N$ and compared there.
### Typicality on a horizon (unfolded)

For a trace $\omega$ and $\lambda, L \in \mathbb N$, $\mathrm{TypOn}(\omega, \lambda, L)$ holds iff for **all** $a, b \in \mathbb N$ with $a + \lambda \le b$ and $b \le L$:
$$\sum_{i \in [a,b]} Z_i(\omega) \;<\; \sum_{i \in (a,b)} Y_i(\omega)$$
(strict inequality; adversarial blocks counted over the closed window including both endpoints, uniquely successful rounds over the open window excluding both endpoints; $a = 0$, i.e. round $0$ of the trace, is included).

Edge cases: if $L < \lambda$ there is no admissible window and $\mathrm{TypOn}$ holds vacuously (for every $\omega$). Any admissible window with $b \le a+1$ has an empty open window, so its right side is $0$ and the strict inequality fails; hence for $\lambda = 0$, $\mathrm{TypOn}(\omega,0,L)$ is false for every $\omega$ and every $L$, and for $\lambda = 1$ it is false for every $\omega$ as soon as $L \ge 1$.
