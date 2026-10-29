# Read-back: `BitcoinBackboneProb.typicalTrunc_failure_le`

**Statement.** Let $n, t \in \mathbb N$, $p \in [0,1]$ and $\lambda, L \in \mathbb N$. Assume

- $\lambda \ge 2$;
- $m(n,t,p) > 0$;
- $4\,t\,p \le (\lambda - 3)\, m(n,t,p)$ (real arithmetic; $\lambda - 3$ may be negative).

Then
$$P_{n,t,p}\big(\{\omega : \text{not } \mathrm{TypTrunc}(\omega, \lambda, L)\}\big) \;\le\; (L+1)^2 \, \exp\!\big(-\kappa(n,t,p)\,(\lambda+1)\big),$$
with $L, \lambda$ cast to $\mathbb R$. Here $\mathrm{TypTrunc}(\omega,\lambda,L)$ is typicality (over **all** windows $[a,b]$ with $a+\lambda \le b$, of unbounded position) of the execution induced by $\omega$ with horizon $L$, in which honest successes in rounds $1,\dots,L$ and adversarial counts in rounds $0,\dots,L$ come from the trace, nobody honest mines in round $0$, and after round $L$ exactly party $0$ mines each round while the adversary finds nothing (both unfolded below).

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
### Deterministic executions (unfolded)

- **Blocks and chains.** A block is either $\mathrm{honest}(q, r)$ (with $q, r \in \mathbb N$; "found by honest party $q$ in round $r$") or $\mathrm{adv}(r, j)$ (with $r, j \in \mathbb N$; "the $j$-th adversarial block of round $r$"). The round of a block is its $r$. A chain is a finite list of blocks (oldest first; the empty list is allowed).
- **Executions.** An execution $E$ consists of: a number $E.n \in \mathbb N$; a function $\mathrm{mined}_E : \mathbb N \times \mathbb N \to \{\mathrm{true},\mathrm{false}\}$ ($\mathrm{mined}_E(q,r)$: party $q$ found a block in round $r$); a function $Z^E : \mathbb N \to \mathbb N$ (adversarial block count per round); and two functions $\mathrm{base}_E, \mathrm{advParent}_E : \mathbb N \times \mathbb N \to \text{Chain}$. Derived notions:
  - honest chain at the end of round $r$: $\mathrm{chain}_E(q, 0) = [\,]$ and $\mathrm{chain}_E(q, r+1) = \mathrm{base}_E(q, r+1)$ followed by the block $\mathrm{honest}(q, r+1)$ if $\mathrm{mined}_E(q, r+1)$, else just $\mathrm{base}_E(q, r+1)$;
  - $\#^E_H(r) = \#\{\, q \in \{0,\dots,E.n - 1\} : \mathrm{mined}_E(q, r) \,\}$, and $Y^E_r = 1$ if $\#^E_H(r) = 1$, else $0$;
  - $E$ *extends* a chain $C$ by block $B$: if $B = \mathrm{honest}(q,r)$, this means $q < E.n$, $\mathrm{mined}_E(q,r) = \mathrm{true}$ and $C = \mathrm{base}_E(q,r)$; if $B = \mathrm{adv}(r,j)$, it means $j < Z^E_r$ and $C = \mathrm{advParent}_E(r,j)$;
  - a chain $C = (C_0, \dots, C_{\ell-1})$ is *valid* for $E$ iff for every $i < \ell$, $C_i$ extends the prefix $(C_0,\dots,C_{i-1})$ in the above sense (in particular $C_0$ extends the empty chain).
- **Typical execution.** $\mathrm{Typical}(E, \lambda)$ holds iff for **all** $a, b \in \mathbb N$ with $a + \lambda \le b$ (no upper bound on $b$):
$$\sum_{i \in [a,b]} Z^E_i \;<\; \sum_{i \in (a,b)} Y^E_i .$$
It depends only on $E.n$, $\mathrm{mined}_E$ and $Z^E$, not on $\mathrm{base}_E, \mathrm{advParent}_E$. Edge case: if $\lambda \le 1$ the window $a = 0$, $b = \lambda$ has an empty open window, so $\mathrm{Typical}(E,\lambda)$ is false for every execution $E$.
- **Legal execution.** $\mathrm{Legal}(E)$ is the conjunction of the following six conditions:
  1. $\mathrm{mined}_E(q, 0) = \mathrm{false}$ for every $q \in \mathbb N$;
  2. for all $q < E.n$ and $r \ge 1$, $\mathrm{base}_E(q, r)$ is a valid chain;
  3. for all $q < E.n$, all $r$, every block of $\mathrm{base}_E(q,r)$ has round $< r$ (so $\mathrm{base}_E(q,0)$ is empty);
  4. for all $q, q' < E.n$ and all $r$: the length of $\mathrm{chain}_E(q', r)$ is at most the length of $\mathrm{base}_E(q, r+1)$;
  5. for all $r, j$ with $j < Z^E_r$, $\mathrm{advParent}_E(r,j)$ is a valid chain;
  6. for all $r, j$ with $j < Z^E_r$, every block of $\mathrm{advParent}_E(r,j)$ has round $\le r$.
- **Execution induced by a trace.** For a trace $\omega \in \Omega_{n,t}$, a horizon $L \in \mathbb N$ and arbitrary functions $\beta, \alpha : \mathbb N \times \mathbb N \to \text{Chain}$, the execution $E^{\omega,L}[\beta,\alpha]$ has $E.n = n$, $\mathrm{base} = \beta$, $\mathrm{advParent} = \alpha$, and
$$\mathrm{mined}(q,r) = \begin{cases} \mathrm{false} & q \ge n,\\ (\omega_r)_1(q) & q < n,\ 1 \le r \le L,\\ \mathrm{false} & q < n,\ r = 0,\\ \mathrm{true} \text{ iff } q = 0 & q < n,\ r > L,\end{cases}
\qquad
Z^E_r = \begin{cases} Z_r(\omega) & r \le L \ (\text{including } r = 0),\\ 0 & r > L.\end{cases}$$
Consequently $Y^E_r = Y_r(\omega)$ for $1 \le r \le L$, $Y^E_0 = 0$, and for $r > L$: $Y^E_r = 1$ if $n \ge 1$ (only party $0$ mines) and $Y^E_r = 0$ if $n = 0$ (nobody ever mines when $n = 0$). The adversarial count of round $0$ is taken from the trace even though no honest party mines in round $0$. Condition 1 of $\mathrm{Legal}$ holds automatically for these executions; the other conditions depend on $\beta, \alpha$.
- **Truncated typicality.** $\mathrm{TypTrunc}(\omega, \lambda, L) :\iff \mathrm{Typical}(E^{\omega,L}[\beta_0,\alpha_0], \lambda)$ where $\beta_0, \alpha_0$ are the constant functions returning the empty chain. Explicitly: for all $a, b$ with $a + \lambda \le b$ (arbitrarily large $b$, windows may lie partly or wholly beyond $L$),
$$\sum_{i \in [a,b]} Z^E_i < \sum_{i \in (a,b)} Y^E_i$$
with $Z^E, Y^E$ as just described. Edge cases: $\mathrm{TypTrunc}$ is false for every $\omega$ if $\lambda \le 1$ (see above), and also false for every $\omega$ if $n = 0$ (the window $a = L+1$, $b = L+1+\lambda$ gives $0 < 0$).
