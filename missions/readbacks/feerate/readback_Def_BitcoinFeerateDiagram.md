# Read-back: definitions of `Def_BitcoinFeerateDiagram`

All definitions live in a single namespace. The file imports the standard mathematics library and a companion file of replacement definitions (FeeRate, getFee, Tx, Replacement, totalFee, PaysForRBF), none of which are used by the definitions below. All arithmetic is in the unbounded integers $\mathbb Z$ or the rationals $\mathbb Q$.

**Division conventions.** Three kinds of division occur.

- *Default integer division* $n \mathbin{/} d$ with remainder $n \bmod d$ (Euclidean convention). For $d > 0$: $n / d = \lfloor n/d \rfloor$ and $n \bmod d = n - d\lfloor n/d \rfloor \in [0, d)$, also for negative $n$ (e.g. $-7/2 = -4$, $-7 \bmod 2 = 1$). For $d < 0$: $n / d = -\lfloor n/|d| \rfloor$ and $n \bmod d \in [0, |d|)$. For $d = 0$: $n / 0 = 0$ and $n \bmod 0 = n$.
- *Truncated division* $\operatorname{tdiv}(n,d)$ with remainder $\operatorname{tmod}(n,d) = n - d\cdot\operatorname{tdiv}(n,d)$: the quotient is rounded toward zero, so the remainder is $0$ or has the sign of $n$, with $|\operatorname{tmod}(n,d)| < |d|$ (e.g. $\operatorname{tdiv}(-7,2) = -3$, $\operatorname{tmod}(-7,2) = -1$). For $d = 0$: $\operatorname{tdiv}(n,0) = 0$, $\operatorname{tmod}(n,0) = n$.
- *Rational division* in $\mathbb Q$, with the convention $q / 0 = 0$. For $q \in \mathbb Q$, $\lfloor q \rfloor$ is the greatest integer $\le q$ and $\lceil q \rceil$ the least integer $\ge q$.

Below, $[P]$ denotes $1$ if the condition $P$ holds and $0$ otherwise.

## The definitions, in order

**1. FeeFrac.** A *FeeFrac* is a structure with two fields, $\mathrm{fee}(X) \in \mathbb Z$ and $\mathrm{size}(X) \in \mathbb Z$, both completely arbitrary integers (zero, negative or huge values allowed; no machine-word bounds, and no requirement that the size be positive or that a zero size forces a zero fee). Equality of FeeFracs is decidable (componentwise) and they have a printable representation.

**2. Zero.** The zero FeeFrac is $0 = (0, 0)$.

**3. Addition.** $X + Y = \big(\mathrm{fee}(X) + \mathrm{fee}(Y),\ \mathrm{size}(X) + \mathrm{size}(Y)\big)$.

**4. Subtraction.** $X - Y = \big(\mathrm{fee}(X) - \mathrm{fee}(Y),\ \mathrm{size}(X) - \mathrm{size}(Y)\big)$.

**5. IsEmpty.** $\mathrm{IsEmpty}(X)$ is the proposition $\mathrm{size}(X) = 0$ (regardless of the fee).

**6. mul.** $\mathrm{mul}(a, b) = a \cdot b$, the exact product of two integers.

**7. mulFallback.** For integers $a, b$, with default (floor) integer division by $2^{32} = 4294967296$:
$$\ell = (a \bmod 2^{32}) \cdot b,\qquad h = (a / 2^{32}) \cdot b,\qquad \mathrm{mulFallback}(a,b) = \big(h + \ell / 2^{32},\ \ell \bmod 2^{32}\big).$$
Here $a \bmod 2^{32} \in [0, 2^{32})$ and $a / 2^{32} = \lfloor a / 2^{32} \rfloor$ also for negative $a$; the second output component lies in $[0, 2^{32})$. No bounds on $a, b$ are assumed.

**8. div.** For integers $n, d$ and a boolean $\rho$ ("round down"), with $q = \operatorname{tdiv}(n,d)$ and $r = \operatorname{tmod}(n,d)$ (truncated division):
$$\mathrm{div}(n, d, \rho) = q + [\,r > 0\,] - [\,r \neq 0 \text{ and } \rho\,].$$
Case by case: if $r = 0$ the result is $q$; if $r > 0$ it is $q$ when $\rho$ is true and $q + 1$ when $\rho$ is false; if $r < 0$ it is $q - 1$ when $\rho$ is true and $q$ when $\rho$ is false. The definition places no condition on $d$: for $d = 0$ it gives $q = 0$, $r = n$, hence $[n > 0] - [n \ne 0 \text{ and } \rho]$; for $d < 0$ the remainder still carries the sign of $n$.

**9. divFallback.** For a pair of integers $n = (n_1, n_2)$, an integer $d$ and a boolean $\rho$, using truncated division throughout:
$$q_H = \operatorname{tdiv}(n_1, d),\quad n_L = \operatorname{tmod}(n_1, d)\cdot 2^{32} + n_2,\quad q_L = \operatorname{tdiv}(n_L, d),\quad r_L = \operatorname{tmod}(n_L, d),$$
$$q_L' = q_L + [\,r_L > 0\,] - [\,r_L \ne 0 \text{ and } \rho\,],\qquad \mathrm{divFallback}(n, d, \rho) = q_H \cdot 2^{32} + q_L'.$$
No range restriction is placed on $n_2$ (it may be negative or $\ge 2^{32}$) or on $d$.

**10. ceilDiv.** For integers $n, d$, with default (Euclidean) integer division:
$$\mathrm{ceilDiv}(n, d) = n / d + [\,n \bmod d \ne 0\,].$$
The definition is stated for all integers (not only nonnegative ones); for $d = 0$ it gives $[\,n \ne 0\,]$.

**11. evaluateFee.** For a FeeFrac $X$, an integer $t$ and a boolean $\rho$:
$$\mathrm{evaluateFee}(X, t, \rho) = \begin{cases} \big(\mathrm{fee}(X)\cdot t\big) \mathbin{/} \mathrm{size}(X) & \text{if } 0 \le \mathrm{fee}(X) < 2^{33} \text{ and } \rho \text{ is true},\\ \mathrm{ceilDiv}\big(\mathrm{fee}(X)\cdot t,\ \mathrm{size}(X)\big) & \text{if } 0 \le \mathrm{fee}(X) < 2^{33} \text{ and } \rho \text{ is false},\\ \mathrm{div}\big(\mathrm{mul}(\mathrm{fee}(X), t),\ \mathrm{size}(X),\ \rho\big) & \text{if } \mathrm{fee}(X) < 0 \text{ or } \mathrm{fee}(X) \ge 2^{33},\end{cases}$$
where $2^{33} = 8589934592$ and "$/$" in the first line is the default (Euclidean) integer division. No condition on $\mathrm{size}(X)$ (it may be $0$ or negative) or on $t$ is part of the definition.

**12. evaluateFeeDown.** $\mathrm{evaluateFeeDown}(X, t) = \mathrm{evaluateFee}(X, t, \text{true})$.

**13. evaluateFeeUp.** $\mathrm{evaluateFeeUp}(X, t) = \mathrm{evaluateFee}(X, t, \text{false})$.

**14. byRatioCmp.** For FeeFracs $X, Y$, $\mathrm{byRatioCmp}(X, Y)$ is the three-way comparison of the two integers $\mathrm{fee}(X)\cdot\mathrm{size}(Y)$ and $\mathrm{fee}(Y)\cdot\mathrm{size}(X)$:
$$\mathrm{byRatioCmp}(X,Y) = \begin{cases}\mathrm{lt} & \text{if } \mathrm{fee}(X)\,\mathrm{size}(Y) < \mathrm{fee}(Y)\,\mathrm{size}(X),\\ \mathrm{eq} & \text{if they are equal},\\ \mathrm{gt} & \text{if } \mathrm{fee}(X)\,\mathrm{size}(Y) > \mathrm{fee}(Y)\,\mathrm{size}(X).\end{cases}$$
No sign condition on the sizes is part of the definition. In particular, $\mathrm{byRatioCmp}(X, (0,1))$ is the comparison of $\mathrm{fee}(X)$ with $0$, independent of $\mathrm{size}(X)$.

**15. ratio.** $\mathrm{ratio}(X) = \mathrm{fee}(X) / \mathrm{size}(X) \in \mathbb Q$, rational division, which yields $0$ when $\mathrm{size}(X) = 0$.

**16. PartialOrdering.** A type with exactly four values: $\mathsf{less}$, $\mathsf{equivalent}$, $\mathsf{greater}$, $\mathsf{unordered}$ (with decidable equality).

**17. boolCompare.** For booleans $\beta_0, \beta_1$:
$$\mathrm{boolCompare}(\text{false},\text{false}) = \mathsf{equivalent},\quad \mathrm{boolCompare}(\text{false},\text{true}) = \mathsf{less},\quad \mathrm{boolCompare}(\text{true},\text{false}) = \mathsf{greater},\quad \mathrm{boolCompare}(\text{true},\text{true}) = \mathsf{equivalent}.$$

**18. sweep.** $\mathrm{sweep}(R_0, R_1, A_0, A_1, \beta_0, \beta_1) \in \mathrm{PartialOrdering}$, where $R_0, R_1$ are lists of FeeFracs, $A_0, A_1$ are FeeFracs and $\beta_0, \beta_1$ are booleans, is defined by recursion (each recursive call shortens $R_0$ or $R_1$, so it terminates) as follows.

1. **Both lists empty** ($R_0 = R_1 = [\,]$): the result is $\mathrm{boolCompare}(\beta_0, \beta_1)$.
2. **$R_0 = c_0 :: R_0'$ nonempty, $R_1 = [\,]$:** put $P = c_0 + A_0$ and $\kappa = \mathrm{byRatioCmp}(P - A_1, (0,1))$, i.e. the comparison of $\mathrm{fee}(P) - \mathrm{fee}(A_1) = \mathrm{fee}(c_0) + \mathrm{fee}(A_0) - \mathrm{fee}(A_1)$ with $0$ (sizes play no role). Set $\beta_0' = \beta_0 \lor (\kappa = \mathrm{gt})$, i.e. $\beta_0$ or $\mathrm{fee}(P) > \mathrm{fee}(A_1)$; and $\beta_1' = \beta_1 \lor (\kappa = \mathrm{lt})$, i.e. $\beta_1$ or $\mathrm{fee}(P) < \mathrm{fee}(A_1)$. If $\beta_0'$ and $\beta_1'$ are both true, the result is $\mathsf{unordered}$; otherwise it is $\mathrm{sweep}(R_0', [\,], P, A_1, \beta_0', \beta_1')$.
3. **$R_0 = [\,]$, $R_1 = c_1 :: R_1'$ nonempty** (mirror image): put $P = c_1 + A_1$ and $\kappa = $ comparison of $\mathrm{fee}(P) - \mathrm{fee}(A_0)$ with $0$. Set $\beta_1' = \beta_1 \lor (\mathrm{fee}(P) > \mathrm{fee}(A_0))$ and $\beta_0' = \beta_0 \lor (\mathrm{fee}(P) < \mathrm{fee}(A_0))$. If both are true, the result is $\mathsf{unordered}$; otherwise it is $\mathrm{sweep}([\,], R_1', A_0, P, \beta_0', \beta_1')$.
4. **Both nonempty**, $R_0 = c_0 :: R_0'$, $R_1 = c_1 :: R_1'$: put $P_0 = c_0 + A_0$ and $P_1 = c_1 + A_1$.
   - **(a) If $\mathrm{size}(P_0) > \mathrm{size}(P_1)$:** $\kappa = \mathrm{byRatioCmp}(P_1 - A_0,\ P_0 - A_0)$, i.e. the comparison of
     $$\big(\mathrm{fee}(P_1) - \mathrm{fee}(A_0)\big)\big(\mathrm{size}(P_0) - \mathrm{size}(A_0)\big) \quad\text{with}\quad \big(\mathrm{fee}(P_0) - \mathrm{fee}(A_0)\big)\big(\mathrm{size}(P_1) - \mathrm{size}(A_0)\big).$$
     Set $\beta_1' = \beta_1 \lor (\kappa = \mathrm{gt})$ and $\beta_0' = \beta_0 \lor (\kappa = \mathrm{lt})$. If both are true, the result is $\mathsf{unordered}$; otherwise it is $\mathrm{sweep}(c_0 :: R_0',\ R_1',\ A_0,\ P_1,\ \beta_0', \beta_1')$ (list $0$ and $A_0$ unchanged; the head of list $1$ is consumed and $A_1$ becomes $P_1$).
   - **(b) Otherwise ($\mathrm{size}(P_0) \le \mathrm{size}(P_1)$):** $\kappa = \mathrm{byRatioCmp}(P_0 - A_1,\ P_1 - A_1)$, i.e. the comparison of
     $$\big(\mathrm{fee}(P_0) - \mathrm{fee}(A_1)\big)\big(\mathrm{size}(P_1) - \mathrm{size}(A_1)\big) \quad\text{with}\quad \big(\mathrm{fee}(P_1) - \mathrm{fee}(A_1)\big)\big(\mathrm{size}(P_0) - \mathrm{size}(A_1)\big).$$
     Set $\beta_0' = \beta_0 \lor (\kappa = \mathrm{gt})$ and $\beta_1' = \beta_1 \lor (\kappa = \mathrm{lt})$. If both are true, the result is $\mathsf{unordered}$. Otherwise, if $\mathrm{size}(P_1) = \mathrm{size}(P_0)$ the result is $\mathrm{sweep}(R_0', R_1', P_0, P_1, \beta_0', \beta_1')$ (both heads consumed); and if $\mathrm{size}(P_0) < \mathrm{size}(P_1)$ it is $\mathrm{sweep}(R_0',\ c_1 :: R_1',\ P_0,\ A_1,\ \beta_0', \beta_1')$.

The flags only ever change from false to true, and the function returns $\mathsf{unordered}$ at the first step at which both become true; a recursive call is made only when at most one of them is true. The case $\mathrm{boolCompare}(\text{true},\text{true}) = \mathsf{equivalent}$ can therefore be reached only if sweep is entered with both flags already true and both lists empty. The definition makes no assumption on signs of fees or sizes, nor on the order of the chunks; zero or negative sizes simply enter the comparisons above.

**19. compareChunks.** For chunk lists (finite lists of FeeFracs, possibly empty) $c^0, c^1$:
$$\mathrm{compareChunks}(c^0, c^1) = \mathrm{sweep}\big(c^0, c^1, (0,0), (0,0), \text{false}, \text{false}\big).$$
In particular $\mathrm{compareChunks}([\,],[\,]) = \mathrm{boolCompare}(\text{false},\text{false}) = \mathsf{equivalent}$, and once one list is exhausted only fees are compared (cases 2 and 3 of sweep).

**20. ImprovesFeerateDiagram.** For chunk lists $\mathit{old}, \mathit{new}$ (in this argument order), $\mathrm{ImprovesFeerateDiagram}(\mathit{old}, \mathit{new})$ is the proposition
$$\mathrm{compareChunks}(\mathit{new}, \mathit{old}) = \mathsf{greater},$$
i.e. the second argument is passed first to compareChunks.

**21. diagram.** For a chunk list $c$ and $x \in \mathbb Q$, $\mathrm{diagram}(c, x) \in \mathbb Q$ is defined recursively:
$$\mathrm{diagram}([\,], x) = 0, \qquad \mathrm{diagram}(c_1 :: c', x) = \begin{cases} \mathrm{fee}(c_1)\cdot x / \mathrm{size}(c_1) & \text{if } x \le \mathrm{size}(c_1),\\ \mathrm{fee}(c_1) + \mathrm{diagram}\big(c', x - \mathrm{size}(c_1)\big) & \text{if } x > \mathrm{size}(c_1),\end{cases}$$
with rational division ($\cdot/0 = 0$). It is defined for every rational $x$, including negative $x$. For the empty list it is identically $0$. When every size is positive, writing $S_k = \sum_{i \le k}\mathrm{size}(c_i)$ and $F_k = \sum_{i \le k}\mathrm{fee}(c_i)$ (with $S_0 = F_0 = 0$) for $c = [c_1,\dots,c_n]$, $n \ge 1$, the recursion unfolds to: $\mathrm{diagram}(c,x) = \mathrm{fee}(c_1)\,x/\mathrm{size}(c_1)$ for all $x \le S_1$ (including negative $x$); $F_{k-1} + \mathrm{fee}(c_k)(x - S_{k-1})/\mathrm{size}(c_k)$ for $S_{k-1} \le x \le S_k$; and $F_n$ for $x \ge S_n$ — the piecewise-linear function through $(0,0), (S_1,F_1), \dots, (S_n,F_n)$, horizontal to the right. If a size is zero or negative the recursion still evaluates but need not have this shape (e.g. a chunk with $\mathrm{size}(c_1) < 0$ gives $\mathrm{diagram}(c, 0) = \mathrm{fee}(c_1) + \mathrm{diagram}(c', -\mathrm{size}(c_1))$; a chunk with size $0$ contributes a jump of $\mathrm{fee}(c_1)$ just after $x = 0$).

**22. diagramFee.** $\mathrm{diagramFee}([c_1,\dots,c_n]) = \sum_{i=1}^n \mathrm{fee}(c_i) \in \mathbb Z$ ($0$ for the empty list).

**23. diagramSize.** $\mathrm{diagramSize}([c_1,\dots,c_n]) = \sum_{i=1}^n \mathrm{size}(c_i) \in \mathbb Z$ ($0$ for the empty list).

**24. SizesPos.** $\mathrm{SizesPos}(c)$: every chunk $c_i$ of $c$ has $\mathrm{size}(c_i) > 0$ (vacuously true for the empty list; nothing is said about fees).

**25. FeeratesNonIncreasing.** $\mathrm{FeeratesNonIncreasing}(c)$ means: for every pair of *adjacent* chunks $c_i, c_{i+1}$,
$$\mathrm{fee}(c_{i+1})\cdot\mathrm{size}(c_i) \le \mathrm{fee}(c_i)\cdot\mathrm{size}(c_{i+1})$$
(integer cross-multiplication). It holds automatically for lists of length $0$ or $1$.

**26. Dominates.** $\mathrm{Dominates}(c^0, c^1)$: for every rational $x \ge 0$, $\mathrm{diagram}(c^1, x) \le \mathrm{diagram}(c^0, x)$.

**27. BetterSomewhere.** $\mathrm{BetterSomewhere}(c^0, c^1)$: there exists a rational $x \ge 0$ with $\mathrm{diagram}(c^1, x) < \mathrm{diagram}(c^0, x)$.

**28. StrictlyBetter.** $\mathrm{StrictlyBetter}(c^0, c^1)$: $\mathrm{Dominates}(c^0, c^1)$ and $\mathrm{BetterSomewhere}(c^0, c^1)$.

In 26–28 only rational $x \ge 0$ are considered ($x = 0$ included, negative $x$ excluded), over the whole half-line, including points beyond both lists' total sizes.
