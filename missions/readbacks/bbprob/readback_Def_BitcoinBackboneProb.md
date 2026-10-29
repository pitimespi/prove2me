# Read-back: `Def_BitcoinBackboneProb` (namespace `BitcoinBackboneProb`)

The file imports Mathlib and the deterministic backbone file (whose definitions used here — blocks, chains, executions, `Typical`, `Legal` — are unfolded in the last section). Throughout, $n, t \in \mathbb N$ are arbitrary (possibly $0$) and $p$ ranges over the closed unit interval $[0,1]$ (endpoints included), used as a real number in arithmetic. One paragraph per declaration, in file order.

**1. `ber`.** For $p \in [0,1]$, $\mathrm{ber}_p$ is the measure on $\{\mathrm{true},\mathrm{false}\}$ given by Mathlib's two-point Bernoulli measure `bernoulliMeasure true false p`: mass $p$ on $\mathrm{true}$ and $1-p$ on $\mathrm{false}$.

**2. `ber_isProbabilityMeasure` (instance).** Registers (with proof) that $\mathrm{ber}_p$ is a probability measure for every $p \in [0,1]$.

**3. `Round`.** $\mathcal R_{n,t}$ is the set of pairs $\rho = (\rho_1, \rho_2)$ with $\rho_1 : \{0,\dots,n-1\} \to \{\mathrm{true},\mathrm{false}\}$ and $\rho_2 : \{0,\dots,t-1\} \to \{\mathrm{true},\mathrm{false}\}$. For $n = 0$ (resp. $t = 0$) the first (resp. second) component has only the empty function. It carries the product $\sigma$-algebra (all subsets of the finite set, since $\{\mathrm{true},\mathrm{false}\}$ is discrete).

**4. `roundMeasure`.** $\mu_{n,t,p}$ is the product measure
$$\mu_{n,t,p} = \Big(\bigotimes_{i=0}^{n-1} \mathrm{ber}_p\Big) \otimes \Big(\bigotimes_{j=0}^{t-1} \mathrm{ber}_p\Big)$$
on $\mathcal R_{n,t}$: all $n + t$ coordinates are independent, each $\mathrm{true}$ with probability $p$. (An empty product is the Dirac mass on the empty function.)

**5. `roundMeasure_isProbabilityMeasure` (instance).** Registers (with proof) that $\mu_{n,t,p}$ is a probability measure.

**6. `Trace`.** $\Omega_{n,t} = \mathcal R_{n,t}^{\mathbb N}$: sequences $\omega = (\omega_0, \omega_1, \dots)$ of round outcomes indexed by all $r \in \mathbb N$, starting at $r = 0$, with the product $\sigma$-algebra.

**7. `P`.** $P_{n,t,p} = \bigotimes_{r \in \mathbb N} \mu_{n,t,p}$, the infinite product measure on $\Omega_{n,t}$ (Mathlib's `Measure.infinitePi`): the coordinates $\omega_r$ are i.i.d. with law $\mu_{n,t,p}$. In the theorems, $P_{n,t,p}(A)$ "as a real" means the extended-nonnegative measure of $A$ converted to $\mathbb R$; it is defined for every set $A$ (outer measure for non-measurable $A$) and lies in $[0,1]$.

**8. `P_isProbabilityMeasure` (instance).** Registers (with proof) that $P_{n,t,p}$ is a probability measure.

**9. `honestCount`.** For $\rho \in \mathcal R_{n,t}$, $\#_H(\rho) = \#\{\, i < n : \rho_1(i) = \mathrm{true}\,\} \in \{0,\dots,n\}$, a natural number.

**10. `advCount`.** For $\rho \in \mathcal R_{n,t}$, $\#_A(\rho) = \#\{\, j < t : \rho_2(j) = \mathrm{true}\,\} \in \{0,\dots,t\}$, a natural number.

**11. `roundX`.** $x(\rho) = 1$ if $\#_H(\rho) > 0$, else $0$ (a natural number).

**12. `roundY`.** $y(\rho) = 1$ if $\#_H(\rho) = 1$, else $0$ (a natural number).

**13. `roundW`.** $w(\rho) = \#_A(\rho) - y(\rho)$, computed in $\mathbb R$ (both terms cast to reals, so no truncation; values in $[-1, t]$).

**14. `X`.** For a trace $\omega$ and any $r \in \mathbb N$ (including $r = 0$), $X_r(\omega) = x(\omega_r) \in \{0,1\}$.

**15. `Y`.** $Y_r(\omega) = y(\omega_r) \in \{0,1\}$, for every $r \in \mathbb N$.

**16. `Z`.** $Z_r(\omega) = \#_A(\omega_r) \in \{0,\dots,t\}$, for every $r \in \mathbb N$.

**17. `W`.** $W_r(\omega) = w(\omega_r) = Z_r(\omega) - Y_r(\omega) \in \mathbb R$, for every $r \in \mathbb N$.

**18. `margin`.** The real number
$$m(n,t,p) = n\,p\,(1-p)^{\,n \,\dot-\, 1} - t\,p,$$
where $n, t$ are cast to $\mathbb R$ and the exponent $n \dot- 1$ is natural-number subtraction truncated at $0$. Edge values: $n = 0$ gives exponent $0$ and $m = -tp$; $n = 1$ gives $m = p - tp$ (with $0^0 = 1$, also at $p = 1$); for $n \ge 2$ and $p = 1$, $m = -t$; for $p = 0$, $m = 0$. No sign is imposed.

**19. `rate`.** The real number
$$\kappa(n,t,p) = \frac{m(n,t,p)^2}{2\,(t+1)^2},$$
always $\ge 0$ (and $= 0$ exactly when $m = 0$); the denominator is at least $2$.

**20. `TypicalOn`.** For a trace $\omega$ and $\lambda, L \in \mathbb N$, $\mathrm{TypOn}(\omega,\lambda,L)$ is the proposition: for **all** $a, b \in \mathbb N$ with $a + \lambda \le b$ and $b \le L$,
$$\sum_{i = a}^{b} Z_i(\omega) \;<\; \sum_{i = a+1}^{b-1} Y_i(\omega)$$
(closed window $\{a,\dots,b\}$ on the left, open window $\{a+1,\dots,b-1\}$ on the right, which is empty when $b \le a+1$; sums in $\mathbb N$; strict inequality; $a = 0$ allowed). Edge cases: if $L < \lambda$ there are no admissible windows and the proposition holds vacuously; for $\lambda = 0$ it is false for every $\omega$ and every $L$ (window $a = b = 0$ gives $Z_0 < 0$); for $\lambda = 1$ it is false for every $\omega$ whenever $L \ge 1$ (window $a=0,b=1$ has empty right-hand sum).

**21. `toExecution`.** For a trace $\omega \in \Omega_{n,t}$, a horizon $L \in \mathbb N$, and arbitrary functions $\beta, \alpha : \mathbb N \times \mathbb N \to \text{Chain}$, $E^{\omega,L}[\beta,\alpha]$ is the deterministic execution with number of honest parties $n$, $\mathrm{base} = \beta$, $\mathrm{advParent} = \alpha$, and
$$\mathrm{mined}(q,r) = \begin{cases} \mathrm{false} & q \ge n,\\ (\omega_r)_1(q) & q < n,\ 1 \le r \le L,\\ \mathrm{false} & q < n,\ r = 0,\\ \mathrm{true} \text{ iff } q = 0 & q < n,\ r > L,\end{cases}
\qquad
Z^E_r = \begin{cases} Z_r(\omega) & r \le L,\\ 0 & r > L.\end{cases}$$
So honest successes come from the trace for rounds $1, \dots, L$ only (round $0$: nobody mines), while the adversarial count comes from the trace for rounds $0, \dots, L$ (round $0$ included). After the horizon, party $0$ alone mines in every round (if $n \ge 1$; if $n = 0$ nobody ever mines) and the adversary finds nothing. Hence the execution's uniquely-successful indicator is $Y^E_r = Y_r(\omega)$ for $1 \le r \le L$, $Y^E_0 = 0$, and for $r > L$ it is $1$ if $n \ge 1$, $0$ if $n = 0$. When $L = 0$, no round's honest outcome is taken from the trace and only $Z_0(\omega)$ is used.

**22. `TypicalTrunc`.** $\mathrm{TypTrunc}(\omega,\lambda,L)$ is the proposition $\mathrm{Typical}(E^{\omega,L}[\beta_0,\alpha_0], \lambda)$, where $\beta_0, \alpha_0$ are the constant functions returning the empty chain. Unfolded: for **all** $a, b \in \mathbb N$ with $a + \lambda \le b$ (no upper bound $b \le L$; windows may extend past or lie entirely beyond the horizon),
$$\sum_{i=a}^{b} Z^E_i \;<\; \sum_{i=a+1}^{b-1} Y^E_i ,$$
with $Z^E, Y^E$ as in item 21. Edge cases: false for every $\omega$ when $\lambda \le 1$ (window $a = 0$, $b = \lambda$ has empty right-hand sum), and false for every $\omega$ when $n = 0$ (window $a = L+1$, $b = L+1+\lambda$ gives $0 < 0$). The choice $\beta_0, \alpha_0$ does not affect the value, since $\mathrm{Typical}$ does not involve base/parent chains.

## Imported definitions from the deterministic backbone file (unfolded)

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
