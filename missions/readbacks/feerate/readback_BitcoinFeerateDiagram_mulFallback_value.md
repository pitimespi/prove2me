# Read-back: `BitcoinFeerateDiagram.mulFallback_value`

**Statement.** For all integers $a$ and $b$, writing $\mathrm{mulFallback}(a, b) = (H, L)$,
$$H \cdot 2^{32} + L = \mathrm{mul}(a, b) = a\cdot b.$$

**Binders and edge cases.** There are no hypotheses: $a$ and $b$ range over all integers, including negative values and values outside any 64-bit or 32-bit range. The statement concerns only the combined value $H\cdot 2^{32} + L$; it does not separately state the range of $H$ or $L$.

## Definitions used, unfolded

**Division conventions.** Three kinds of division occur.

- *Default integer division* $n \mathbin{/} d$ with remainder $n \bmod d$ (Euclidean convention). For $d > 0$: $n / d = \lfloor n/d \rfloor$ and $n \bmod d = n - d\lfloor n/d \rfloor \in [0, d)$, also for negative $n$ (e.g. $-7/2 = -4$, $-7 \bmod 2 = 1$). For $d < 0$: $n / d = -\lfloor n/|d| \rfloor$ and $n \bmod d \in [0, |d|)$. For $d = 0$: $n / 0 = 0$ and $n \bmod 0 = n$.
- *Truncated division* $\operatorname{tdiv}(n,d)$ with remainder $\operatorname{tmod}(n,d) = n - d\cdot\operatorname{tdiv}(n,d)$: the quotient is rounded toward zero, so the remainder is $0$ or has the sign of $n$, with $|\operatorname{tmod}(n,d)| < |d|$ (e.g. $\operatorname{tdiv}(-7,2) = -3$, $\operatorname{tmod}(-7,2) = -1$). For $d = 0$: $\operatorname{tdiv}(n,0) = 0$, $\operatorname{tmod}(n,0) = n$.
- *Rational division* in $\mathbb Q$, with the convention $q / 0 = 0$. For $q \in \mathbb Q$, $\lfloor q \rfloor$ is the greatest integer $\le q$ and $\lceil q \rceil$ the least integer $\ge q$.

Below, $[P]$ denotes $1$ if the condition $P$ holds and $0$ otherwise.

**mul.** $\mathrm{mul}(a, b) = a \cdot b$, the exact product of two integers.

**mulFallback.** For integers $a, b$, with default (floor) integer division by $2^{32} = 4294967296$:
$$\ell = (a \bmod 2^{32}) \cdot b,\qquad h = (a / 2^{32}) \cdot b,\qquad \mathrm{mulFallback}(a,b) = \big(h + \ell / 2^{32},\ \ell \bmod 2^{32}\big).$$
Here $a \bmod 2^{32} \in [0, 2^{32})$ and $a / 2^{32} = \lfloor a / 2^{32} \rfloor$ also for negative $a$; the second output component lies in $[0, 2^{32})$. No bounds on $a, b$ are assumed.

