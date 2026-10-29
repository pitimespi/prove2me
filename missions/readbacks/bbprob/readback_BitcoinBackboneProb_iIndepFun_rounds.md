# Read-back: `BitcoinBackboneProb.iIndepFun_rounds`

**Statement.** For all $n, t \in \mathbb N$ and all $p \in [0,1]$, with no further hypotheses: the family of coordinate maps $(\omega \mapsto \omega_r)_{r \in \mathbb N}$, each from $\Omega_{n,t}$ to $\mathcal R_{n,t}$ (with the product $\sigma$-algebra on $\mathcal R_{n,t}$), is **mutually independent** under $P_{n,t,p}$. That is, for every finite set of rounds $\{r_1, \dots, r_k\} \subseteq \mathbb N$ (distinct indices) and all measurable sets $A_1, \dots, A_k \subseteq \mathcal R_{n,t}$,
$$P_{n,t,p}\big(\omega_{r_1} \in A_1, \dots, \omega_{r_k} \in A_k\big) = \prod_{i=1}^{k} P_{n,t,p}\big(\omega_{r_i} \in A_i\big).$$
This statement does not by itself assert anything about the law of each $\omega_r$.

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
