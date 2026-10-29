# Read-back: `BitcoinFeerateDiagram.evaluateFeeUp_eq_ceil`

**Statement.** For every FeeFrac $f$ (a pair of integers $(\mathrm{fee}(f), \mathrm{size}(f))$) and every integer $t$ (the "at size"), assuming
$$\mathrm{size}(f) > 0 \qquad\text{and}\qquad t \ge 0,$$
we have
$$\mathrm{evaluateFeeUp}(f, t) = \left\lceil \frac{\mathrm{fee}(f)\cdot t}{\mathrm{size}(f)} \right\rceil,$$
where the product $\mathrm{fee}(f)\cdot t$ is formed in $\mathbb Z$, then divided exactly in $\mathbb Q$ by $\mathrm{size}(f)$, and the ceiling is taken.

**Binders and edge cases.** $\mathrm{fee}(f)$ is an arbitrary integer (negative, zero, or $\ge 2^{33}$ all allowed), so all three branches of evaluateFee are in scope (here with $\rho$ false: the ceilDiv branch for $0 \le \mathrm{fee}(f) < 2^{33}$ and the div branch otherwise). The hypothesis $t \ge 0$ carries a name beginning with an underscore, which only signals that the name is not referred to; it is nevertheless a hypothesis of the theorem, so the statement says nothing about negative $t$. $t = 0$ is allowed. No word-size bounds are imposed on fee, size or $t$.

## Definitions used, unfolded

**Division conventions.** Three kinds of division occur.

- *Default integer division* $n \mathbin{/} d$ with remainder $n \bmod d$ (Euclidean convention). For $d > 0$: $n / d = \lfloor n/d \rfloor$ and $n \bmod d = n - d\lfloor n/d \rfloor \in [0, d)$, also for negative $n$ (e.g. $-7/2 = -4$, $-7 \bmod 2 = 1$). For $d < 0$: $n / d = -\lfloor n/|d| \rfloor$ and $n \bmod d \in [0, |d|)$. For $d = 0$: $n / 0 = 0$ and $n \bmod 0 = n$.
- *Truncated division* $\operatorname{tdiv}(n,d)$ with remainder $\operatorname{tmod}(n,d) = n - d\cdot\operatorname{tdiv}(n,d)$: the quotient is rounded toward zero, so the remainder is $0$ or has the sign of $n$, with $|\operatorname{tmod}(n,d)| < |d|$ (e.g. $\operatorname{tdiv}(-7,2) = -3$, $\operatorname{tmod}(-7,2) = -1$). For $d = 0$: $\operatorname{tdiv}(n,0) = 0$, $\operatorname{tmod}(n,0) = n$.
- *Rational division* in $\mathbb Q$, with the convention $q / 0 = 0$. For $q \in \mathbb Q$, $\lfloor q \rfloor$ is the greatest integer $\le q$ and $\lceil q \rceil$ the least integer $\ge q$.

Below, $[P]$ denotes $1$ if the condition $P$ holds and $0$ otherwise.

**FeeFrac.** A *FeeFrac* is a pair $X = (\mathrm{fee}(X), \mathrm{size}(X))$ of two arbitrary integers. Nothing constrains them: either component may be zero or negative, and no machine-word bounds are imposed. Addition and subtraction are componentwise,
$$X \pm Y = \big(\mathrm{fee}(X) \pm \mathrm{fee}(Y),\ \mathrm{size}(X) \pm \mathrm{size}(Y)\big),$$
and the zero FeeFrac is $(0,0)$. A *chunk list* is a finite list $c = [c_1, \dots, c_n]$ of FeeFracs; the empty list ($n = 0$) is allowed.

**mul.** $\mathrm{mul}(a, b) = a \cdot b$, the exact product of two integers.

**div.** For integers $n, d$ and a boolean $\rho$ ("round down"), with $q = \operatorname{tdiv}(n,d)$ and $r = \operatorname{tmod}(n,d)$ (truncated division):
$$\mathrm{div}(n, d, \rho) = q + [\,r > 0\,] - [\,r \neq 0 \text{ and } \rho\,].$$
Case by case: if $r = 0$ the result is $q$; if $r > 0$ it is $q$ when $\rho$ is true and $q + 1$ when $\rho$ is false; if $r < 0$ it is $q - 1$ when $\rho$ is true and $q$ when $\rho$ is false. The definition places no condition on $d$: for $d = 0$ it gives $q = 0$, $r = n$, hence $[n > 0] - [n \ne 0 \text{ and } \rho]$; for $d < 0$ the remainder still carries the sign of $n$.

**ceilDiv.** For integers $n, d$, with default (Euclidean) integer division:
$$\mathrm{ceilDiv}(n, d) = n / d + [\,n \bmod d \ne 0\,].$$
The definition is stated for all integers (not only nonnegative ones); for $d = 0$ it gives $[\,n \ne 0\,]$.

**evaluateFee, evaluateFeeDown, evaluateFeeUp.** For a FeeFrac $X$, an integer $t$ ("at size") and a boolean $\rho$:
$$\mathrm{evaluateFee}(X, t, \rho) = \begin{cases} \big(\mathrm{fee}(X)\cdot t\big) \mathbin{/} \mathrm{size}(X) & \text{if } 0 \le \mathrm{fee}(X) < 2^{33} \text{ and } \rho \text{ is true},\\ \mathrm{ceilDiv}\big(\mathrm{fee}(X)\cdot t,\ \mathrm{size}(X)\big) & \text{if } 0 \le \mathrm{fee}(X) < 2^{33} \text{ and } \rho \text{ is false},\\ \mathrm{div}\big(\mathrm{mul}(\mathrm{fee}(X), t),\ \mathrm{size}(X),\ \rho\big) & \text{otherwise (} \mathrm{fee}(X) < 0 \text{ or } \mathrm{fee}(X) \ge 2^{33}\text{)},\end{cases}$$
where $2^{33} = 8589934592$, the "$/$" in the first line is the default (Euclidean) integer division, and $\mathrm{mul}(a,b) = ab$. Then $\mathrm{evaluateFeeDown}(X, t) = \mathrm{evaluateFee}(X, t, \text{true})$ and $\mathrm{evaluateFeeUp}(X, t) = \mathrm{evaluateFee}(X, t, \text{false})$. The definition itself imposes no condition on $\mathrm{size}(X)$ or $t$.

