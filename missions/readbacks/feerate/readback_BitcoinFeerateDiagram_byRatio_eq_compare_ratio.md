# Read-back: `BitcoinFeerateDiagram.byRatio_eq_compare_ratio`

**Statement.** Let $a$ and $b$ be arbitrary FeeFracs (pairs of integers $(\mathrm{fee}, \mathrm{size})$) and assume
$$\mathrm{size}(a) > 0 \qquad\text{and}\qquad \mathrm{size}(b) > 0.$$
Then the integer cross-multiplication comparison equals the comparison of the rational feerates:
$$\mathrm{byRatioCmp}(a, b) = \mathrm{compare}\big(\mathrm{ratio}(a),\ \mathrm{ratio}(b)\big),$$
i.e. the three-way comparison ($\mathrm{lt}/\mathrm{eq}/\mathrm{gt}$) of the integers $\mathrm{fee}(a)\cdot\mathrm{size}(b)$ and $\mathrm{fee}(b)\cdot\mathrm{size}(a)$ gives the same outcome as the three-way comparison of the rationals $\mathrm{fee}(a)/\mathrm{size}(a)$ and $\mathrm{fee}(b)/\mathrm{size}(b)$.

**Binders and edge cases.** The fees of $a$ and $b$ are unrestricted integers (zero or negative allowed); only the sizes are required to be strictly positive, so the rational divisions never divide by zero. No upper bounds on any of the four integers are assumed. The statement is an equality of three-valued outcomes, so it covers all three cases ($<$, $=$, $>$) at once.

## Definitions used, unfolded

**Division conventions.** Three kinds of division occur.

- *Default integer division* $n \mathbin{/} d$ with remainder $n \bmod d$ (Euclidean convention). For $d > 0$: $n / d = \lfloor n/d \rfloor$ and $n \bmod d = n - d\lfloor n/d \rfloor \in [0, d)$, also for negative $n$ (e.g. $-7/2 = -4$, $-7 \bmod 2 = 1$). For $d < 0$: $n / d = -\lfloor n/|d| \rfloor$ and $n \bmod d \in [0, |d|)$. For $d = 0$: $n / 0 = 0$ and $n \bmod 0 = n$.
- *Truncated division* $\operatorname{tdiv}(n,d)$ with remainder $\operatorname{tmod}(n,d) = n - d\cdot\operatorname{tdiv}(n,d)$: the quotient is rounded toward zero, so the remainder is $0$ or has the sign of $n$, with $|\operatorname{tmod}(n,d)| < |d|$ (e.g. $\operatorname{tdiv}(-7,2) = -3$, $\operatorname{tmod}(-7,2) = -1$). For $d = 0$: $\operatorname{tdiv}(n,0) = 0$, $\operatorname{tmod}(n,0) = n$.
- *Rational division* in $\mathbb Q$, with the convention $q / 0 = 0$. For $q \in \mathbb Q$, $\lfloor q \rfloor$ is the greatest integer $\le q$ and $\lceil q \rceil$ the least integer $\ge q$.

Below, $[P]$ denotes $1$ if the condition $P$ holds and $0$ otherwise.

**FeeFrac.** A *FeeFrac* is a pair $X = (\mathrm{fee}(X), \mathrm{size}(X))$ of two arbitrary integers. Nothing constrains them: either component may be zero or negative, and no machine-word bounds are imposed. Addition and subtraction are componentwise,
$$X \pm Y = \big(\mathrm{fee}(X) \pm \mathrm{fee}(Y),\ \mathrm{size}(X) \pm \mathrm{size}(Y)\big),$$
and the zero FeeFrac is $(0,0)$. A *chunk list* is a finite list $c = [c_1, \dots, c_n]$ of FeeFracs; the empty list ($n = 0$) is allowed.

**byRatioCmp.** For FeeFracs $X, Y$, $\mathrm{byRatioCmp}(X, Y)$ is the three-way comparison of the two integers $\mathrm{fee}(X)\cdot\mathrm{size}(Y)$ and $\mathrm{fee}(Y)\cdot\mathrm{size}(X)$:
$$\mathrm{byRatioCmp}(X,Y) = \begin{cases}\mathrm{lt} & \text{if } \mathrm{fee}(X)\,\mathrm{size}(Y) < \mathrm{fee}(Y)\,\mathrm{size}(X),\\ \mathrm{eq} & \text{if they are equal},\\ \mathrm{gt} & \text{if } \mathrm{fee}(X)\,\mathrm{size}(Y) > \mathrm{fee}(Y)\,\mathrm{size}(X).\end{cases}$$
No sign condition on the sizes is part of the definition. In particular, $\mathrm{byRatioCmp}(X, (0,1))$ is the comparison of $\mathrm{fee}(X)$ with $0$, independent of $\mathrm{size}(X)$.

**ratio.** $\mathrm{ratio}(X) = \mathrm{fee}(X) / \mathrm{size}(X) \in \mathbb Q$ (rational division; equals $0$ when $\mathrm{size}(X) = 0$). For rationals $p, q$, $\mathrm{compare}(p, q)$ is $\mathrm{lt}$, $\mathrm{eq}$ or $\mathrm{gt}$ according as $p < q$, $p = q$ or $p > q$.

