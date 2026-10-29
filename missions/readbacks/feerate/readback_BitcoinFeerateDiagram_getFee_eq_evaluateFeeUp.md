# Read-back: `BitcoinFeerateDiagram.getFee_eq_evaluateFeeUp`

**Statement.** For every FeeRate $r$ — natural numbers $\mathrm{fee}(r) \ge 0$ and $\mathrm{size}(r)$ with the built-in condition $\mathrm{size}(r) > 0$ — and every natural number $v$,
$$\mathrm{getFee}(r, v) = \mathrm{evaluateFeeUp}\big((\mathrm{fee}(r), \mathrm{size}(r)),\ v\big),$$
where the left side, a natural number, is regarded as an integer, and on the right $(\mathrm{fee}(r), \mathrm{size}(r))$ is the FeeFrac whose fee and size are $\mathrm{fee}(r)$ and $\mathrm{size}(r)$ regarded as integers, and $v$ is regarded as an integer.

Unfolded: the left side is $\big(\mathrm{fee}(r)\,v + \mathrm{size}(r) - 1\big) \mathbin{/} \mathrm{size}(r)$ (floor division of natural numbers). Since $\mathrm{fee}(r) \ge 0$, the right side is
$$\begin{cases}\mathrm{ceilDiv}\big(\mathrm{fee}(r)\,v,\ \mathrm{size}(r)\big) = \mathrm{fee}(r)\,v \mathbin{/} \mathrm{size}(r) + [\,\mathrm{fee}(r)\,v \bmod \mathrm{size}(r) \ne 0\,] & \text{if } \mathrm{fee}(r) < 2^{33},\\ \mathrm{div}\big(\mathrm{fee}(r)\,v,\ \mathrm{size}(r),\ \text{false}\big) & \text{if } \mathrm{fee}(r) \ge 2^{33}.\end{cases}$$

**Binders and edge cases.** There are no hypotheses beyond those built into the types: $\mathrm{fee}(r)$ and $v$ are arbitrary natural numbers (including $0$, and arbitrarily large — no word-size bounds), and $\mathrm{size}(r)$ is a positive natural number. Negative fees cannot occur on either side since the FeeRate fee is a natural number.

## Definitions used, unfolded

**Division conventions.** Three kinds of division occur.

- *Default integer division* $n \mathbin{/} d$ with remainder $n \bmod d$ (Euclidean convention). For $d > 0$: $n / d = \lfloor n/d \rfloor$ and $n \bmod d = n - d\lfloor n/d \rfloor \in [0, d)$, also for negative $n$ (e.g. $-7/2 = -4$, $-7 \bmod 2 = 1$). For $d < 0$: $n / d = -\lfloor n/|d| \rfloor$ and $n \bmod d \in [0, |d|)$. For $d = 0$: $n / 0 = 0$ and $n \bmod 0 = n$.
- *Truncated division* $\operatorname{tdiv}(n,d)$ with remainder $\operatorname{tmod}(n,d) = n - d\cdot\operatorname{tdiv}(n,d)$: the quotient is rounded toward zero, so the remainder is $0$ or has the sign of $n$, with $|\operatorname{tmod}(n,d)| < |d|$ (e.g. $\operatorname{tdiv}(-7,2) = -3$, $\operatorname{tmod}(-7,2) = -1$). For $d = 0$: $\operatorname{tdiv}(n,0) = 0$, $\operatorname{tmod}(n,0) = n$.
- *Rational division* in $\mathbb Q$, with the convention $q / 0 = 0$. For $q \in \mathbb Q$, $\lfloor q \rfloor$ is the greatest integer $\le q$ and $\lceil q \rceil$ the least integer $\ge q$.

Below, $[P]$ denotes $1$ if the condition $P$ holds and $0$ otherwise.

**FeeRate and getFee** (from the imported replacement file). A *FeeRate* $r$ consists of natural numbers $\mathrm{fee}(r) \ge 0$ and $\mathrm{size}(r)$ with the built-in requirement $\mathrm{size}(r) > 0$. For $v \in \mathbb N$,
$$\mathrm{getFee}(r, v) = \big(\mathrm{fee}(r)\cdot v + (\mathrm{size}(r) - 1)\big) \mathbin{/} \mathrm{size}(r)$$
computed in the natural numbers with floor division ($\mathrm{size}(r) - 1 \ge 0$ since $\mathrm{size}(r) > 0$).

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

