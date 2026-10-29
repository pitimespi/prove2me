# Read-back: `BitcoinFeerateDiagram.improves_total_fee`

**Statement.** Let $\mathit{old}$ and $\mathit{new}$ be arbitrary finite lists of FeeFracs (possibly empty) such that

- $\mathrm{SizesPos}(\mathit{old})$ and $\mathrm{SizesPos}(\mathit{new})$ (every chunk has strictly positive size), and
- $\mathrm{ImprovesFeerateDiagram}(\mathit{old}, \mathit{new})$, i.e. $\mathrm{compareChunks}(\mathit{new}, \mathit{old}) = \mathsf{greater}$.

Then
$$\mathrm{diagramFee}(\mathit{old}) \le \mathrm{diagramFee}(\mathit{new}), \qquad\text{i.e.}\qquad \sum_{c \in \mathit{old}} \mathrm{fee}(c) \le \sum_{c \in \mathit{new}} \mathrm{fee}(c)$$
(a non-strict inequality of integers).

**Binders and edge cases.** Fees are arbitrary integers (zero or negative allowed); the chunks are not assumed to be sorted by feerate; lengths and total sizes of the two lists are unrelated; either list may be empty (total fee $0$). The conclusion is $\le$, not $<$. Note the argument order: compareChunks is run with $\mathit{new}$ first.

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

**PartialOrdering and boolCompare.** $\mathrm{PartialOrdering}$ is a four-element type with values $\mathsf{less}$, $\mathsf{equivalent}$, $\mathsf{greater}$, $\mathsf{unordered}$. For booleans $\beta_0, \beta_1$:
$$\mathrm{boolCompare}(\text{false},\text{false}) = \mathsf{equivalent},\quad \mathrm{boolCompare}(\text{false},\text{true}) = \mathsf{less},\quad \mathrm{boolCompare}(\text{true},\text{false}) = \mathsf{greater},\quad \mathrm{boolCompare}(\text{true},\text{true}) = \mathsf{equivalent}.$$

**sweep.** $\mathrm{sweep}(R_0, R_1, A_0, A_1, \beta_0, \beta_1) \in \mathrm{PartialOrdering}$, where $R_0, R_1$ are lists of FeeFracs, $A_0, A_1$ are FeeFracs and $\beta_0, \beta_1$ are booleans, is defined by recursion (each recursive call shortens $R_0$ or $R_1$, so it terminates) as follows.

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

**compareChunks.** For chunk lists $c^0, c^1$:
$$\mathrm{compareChunks}(c^0, c^1) = \mathrm{sweep}\big(c^0, c^1, (0,0), (0,0), \text{false}, \text{false}\big).$$
Edge cases: $\mathrm{compareChunks}([\,],[\,]) = \mathsf{equivalent}$; when one list is (or becomes) exhausted, only the fees of the remaining cumulative points versus the other side's accumulated fee are compared (case 2/3 of sweep).

**ImprovesFeerateDiagram.** For chunk lists $\mathit{old}$ and $\mathit{new}$ (in this argument order),
$$\mathrm{ImprovesFeerateDiagram}(\mathit{old}, \mathit{new}) \iff \mathrm{compareChunks}(\mathit{new}, \mathit{old}) = \mathsf{greater},$$
i.e. the *second* argument is passed *first* to compareChunks.

**diagramFee, diagramSize.** For $c = [c_1,\dots,c_n]$: $\mathrm{diagramFee}(c) = \sum_{i=1}^n \mathrm{fee}(c_i) \in \mathbb Z$ and $\mathrm{diagramSize}(c) = \sum_{i=1}^n \mathrm{size}(c_i) \in \mathbb Z$ (both $0$ for the empty list).

**SizesPos.** $\mathrm{SizesPos}(c)$ means $\mathrm{size}(c_i) > 0$ for every chunk $c_i$ in $c$ (vacuously true for the empty list). It says nothing about fees, which may be zero or negative.

