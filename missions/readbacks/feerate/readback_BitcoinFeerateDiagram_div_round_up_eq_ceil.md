# Read-back: `BitcoinFeerateDiagram.div_round_up_eq_ceil`

**Statement.** For all integers $n$ and $d$ with
$$d > 0,$$
$$\mathrm{div}(n, d, \text{false}) = \left\lceil \frac{n}{d} \right\rceil,$$
where $n/d$ is the exact rational quotient and $\lceil\cdot\rceil$ is the least integer not below it (the equality is between integers).

**Binders and edge cases.** $n$ is an arbitrary integer (negative, zero or positive; no word-size bound). Only $d > 0$ is assumed, so $d = 0$ and negative $d$ are excluded. Unfolded, the left side is $\operatorname{tdiv}(n,d) + [\operatorname{tmod}(n,d) > 0]$, i.e. the truncated quotient, plus $1$ exactly when the truncated remainder is positive.

## Definitions used, unfolded

**Division conventions.** Three kinds of division occur.

- *Default integer division* $n \mathbin{/} d$ with remainder $n \bmod d$ (Euclidean convention). For $d > 0$: $n / d = \lfloor n/d \rfloor$ and $n \bmod d = n - d\lfloor n/d \rfloor \in [0, d)$, also for negative $n$ (e.g. $-7/2 = -4$, $-7 \bmod 2 = 1$). For $d < 0$: $n / d = -\lfloor n/|d| \rfloor$ and $n \bmod d \in [0, |d|)$. For $d = 0$: $n / 0 = 0$ and $n \bmod 0 = n$.
- *Truncated division* $\operatorname{tdiv}(n,d)$ with remainder $\operatorname{tmod}(n,d) = n - d\cdot\operatorname{tdiv}(n,d)$: the quotient is rounded toward zero, so the remainder is $0$ or has the sign of $n$, with $|\operatorname{tmod}(n,d)| < |d|$ (e.g. $\operatorname{tdiv}(-7,2) = -3$, $\operatorname{tmod}(-7,2) = -1$). For $d = 0$: $\operatorname{tdiv}(n,0) = 0$, $\operatorname{tmod}(n,0) = n$.
- *Rational division* in $\mathbb Q$, with the convention $q / 0 = 0$. For $q \in \mathbb Q$, $\lfloor q \rfloor$ is the greatest integer $\le q$ and $\lceil q \rceil$ the least integer $\ge q$.

Below, $[P]$ denotes $1$ if the condition $P$ holds and $0$ otherwise.

**div.** For integers $n, d$ and a boolean $\rho$ ("round down"), with $q = \operatorname{tdiv}(n,d)$ and $r = \operatorname{tmod}(n,d)$ (truncated division):
$$\mathrm{div}(n, d, \rho) = q + [\,r > 0\,] - [\,r \neq 0 \text{ and } \rho\,].$$
Case by case: if $r = 0$ the result is $q$; if $r > 0$ it is $q$ when $\rho$ is true and $q + 1$ when $\rho$ is false; if $r < 0$ it is $q - 1$ when $\rho$ is true and $q$ when $\rho$ is false. The definition places no condition on $d$: for $d = 0$ it gives $q = 0$, $r = n$, hence $[n > 0] - [n \ne 0 \text{ and } \rho]$; for $d < 0$ the remainder still carries the sign of $n$.

