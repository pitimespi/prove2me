# Read-back: `BitcoinFeerateDiagram.divFallback_eq_div`

**Statement.** For every pair of integers $n = (n_1, n_2)$, every integer $d$ with
$$d > 0,$$
and every boolean $\rho$,
$$\mathrm{divFallback}\big((n_1, n_2), d, \rho\big) = \mathrm{div}\big(n_1\cdot 2^{32} + n_2,\ d,\ \rho\big).$$

**Binders and edge cases.** The only hypothesis is $d > 0$. There is no restriction on $n_1$ or on $n_2$: in particular $n_2$ may be negative or at least $2^{32}$, and $n_1, n_2$ are not required to come from $\mathrm{mulFallback}$; no word-size bounds are imposed. Both values of $\rho$ (true = "round down", false) are covered. Both sides are computed from truncated division (quotient toward zero, remainder with the sign of the dividend) followed by the correction term described below.

## Definitions used, unfolded

**Division conventions.** Three kinds of division occur.

- *Default integer division* $n \mathbin{/} d$ with remainder $n \bmod d$ (Euclidean convention). For $d > 0$: $n / d = \lfloor n/d \rfloor$ and $n \bmod d = n - d\lfloor n/d \rfloor \in [0, d)$, also for negative $n$ (e.g. $-7/2 = -4$, $-7 \bmod 2 = 1$). For $d < 0$: $n / d = -\lfloor n/|d| \rfloor$ and $n \bmod d \in [0, |d|)$. For $d = 0$: $n / 0 = 0$ and $n \bmod 0 = n$.
- *Truncated division* $\operatorname{tdiv}(n,d)$ with remainder $\operatorname{tmod}(n,d) = n - d\cdot\operatorname{tdiv}(n,d)$: the quotient is rounded toward zero, so the remainder is $0$ or has the sign of $n$, with $|\operatorname{tmod}(n,d)| < |d|$ (e.g. $\operatorname{tdiv}(-7,2) = -3$, $\operatorname{tmod}(-7,2) = -1$). For $d = 0$: $\operatorname{tdiv}(n,0) = 0$, $\operatorname{tmod}(n,0) = n$.
- *Rational division* in $\mathbb Q$, with the convention $q / 0 = 0$. For $q \in \mathbb Q$, $\lfloor q \rfloor$ is the greatest integer $\le q$ and $\lceil q \rceil$ the least integer $\ge q$.

Below, $[P]$ denotes $1$ if the condition $P$ holds and $0$ otherwise.

**div.** For integers $n, d$ and a boolean $\rho$ ("round down"), with $q = \operatorname{tdiv}(n,d)$ and $r = \operatorname{tmod}(n,d)$ (truncated division):
$$\mathrm{div}(n, d, \rho) = q + [\,r > 0\,] - [\,r \neq 0 \text{ and } \rho\,].$$
Case by case: if $r = 0$ the result is $q$; if $r > 0$ it is $q$ when $\rho$ is true and $q + 1$ when $\rho$ is false; if $r < 0$ it is $q - 1$ when $\rho$ is true and $q$ when $\rho$ is false. The definition places no condition on $d$: for $d = 0$ it gives $q = 0$, $r = n$, hence $[n > 0] - [n \ne 0 \text{ and } \rho]$; for $d < 0$ the remainder still carries the sign of $n$.

**divFallback.** For a pair of integers $n = (n_1, n_2)$, an integer $d$ and a boolean $\rho$, using truncated division throughout:
$$q_H = \operatorname{tdiv}(n_1, d),\quad n_L = \operatorname{tmod}(n_1, d)\cdot 2^{32} + n_2,\quad q_L = \operatorname{tdiv}(n_L, d),\quad r_L = \operatorname{tmod}(n_L, d),$$
$$q_L' = q_L + [\,r_L > 0\,] - [\,r_L \ne 0 \text{ and } \rho\,],\qquad \mathrm{divFallback}(n, d, \rho) = q_H \cdot 2^{32} + q_L'.$$
No range restriction is placed on $n_2$ (it may be negative or $\ge 2^{32}$) or on $d$.

