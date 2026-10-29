# Read-back: `BitcoinFeerateDiagram.no_free_relay_diagram`

**Statement.** Let

- $r$ be a FeeRate (natural numbers $\mathrm{fee}(r) \ge 0$, $\mathrm{size}(r) > 0$),
- $R$ be a Replacement (a new transaction $R.\mathrm{new}$ with natural-number fee and positive natural-number vsize, a multiset $R.\mathrm{evicted}$ of transactions, and a sub-multiset $R.\mathrm{direct} \le R.\mathrm{evicted}$),
- $\mathit{old}$ and $\mathit{new}$ be arbitrary finite lists of FeeFracs (possibly empty),
- $F$ be an arbitrary integer,

and assume

1. $\mathrm{SizesPos}(\mathit{old})$ and $\mathrm{SizesPos}(\mathit{new})$: every chunk of either list has strictly positive size;
2. $\mathrm{diagramFee}(\mathit{old}) = F + \mathrm{totalFee}(R.\mathrm{evicted})$ (the natural-number total fee regarded as an integer);
3. $\mathrm{diagramFee}(\mathit{new}) = F + \mathrm{fee}(R.\mathrm{new})$ (regarded as an integer);
4. $\mathrm{ImprovesFeerateDiagram}(\mathit{old}, \mathit{new})$, i.e. $\mathrm{compareChunks}(\mathit{new}, \mathit{old}) = \mathsf{greater}$;
5. $\mathrm{PaysForRBF}(r, R)$, i.e. $\mathrm{totalFee}(R.\mathrm{evicted}) \le \mathrm{fee}(R.\mathrm{new})$ and $\mathrm{getFee}(r, \mathrm{vsize}(R.\mathrm{new})) \le \mathrm{fee}(R.\mathrm{new}) - \mathrm{totalFee}(R.\mathrm{evicted})$.

Then both of the following hold:

- $\mathrm{StrictlyBetter}(\mathit{new}, \mathit{old})$: $\mathrm{diagram}(\mathit{old}, x) \le \mathrm{diagram}(\mathit{new}, x)$ for every rational $x \ge 0$, and $\mathrm{diagram}(\mathit{old}, x) < \mathrm{diagram}(\mathit{new}, x)$ for some rational $x \ge 0$;
- $\displaystyle \mathrm{diagramFee}(\mathit{old}) + \mathrm{getFee}\big(r, \mathrm{vsize}(R.\mathrm{new})\big) \le \mathrm{diagramFee}(\mathit{new})$ (in $\mathbb Z$), where $\mathrm{getFee}(r, v) = \big(\mathrm{fee}(r)\,v + \mathrm{size}(r) - 1\big) \mathbin{/} \mathrm{size}(r)$ with natural-number floor division.

**Binders and edge cases.** The chunk lists are tied to $R$ only through hypotheses 2 and 3, i.e. through their total fees and the common integer offset $F$; nothing relates the chunks' sizes to $\mathrm{vsize}(R.\mathrm{new})$ or to the evicted transactions' vsizes, nothing relates individual chunks to individual transactions, and $R.\mathrm{direct}$ plays no role. $F$ may be any integer (including negative). Chunk fees are arbitrary integers; the lists are not assumed sorted by feerate; either list may be empty (total fee $0$). $R.\mathrm{evicted}$ may be the empty multiset (total fee $0$). The fee rate $r$ may have $\mathrm{fee}(r) = 0$, in which case $\mathrm{getFee} = 0$. Argument order: ImprovesFeerateDiagram takes $\mathit{old}$ first and runs compareChunks with $\mathit{new}$ first.

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

**diagram.** For a chunk list $c$ and $x \in \mathbb Q$, $\mathrm{diagram}(c, x) \in \mathbb Q$ is defined recursively:
$$\mathrm{diagram}([\,], x) = 0, \qquad \mathrm{diagram}(c_1 :: c', x) = \begin{cases} \mathrm{fee}(c_1)\cdot x / \mathrm{size}(c_1) & \text{if } x \le \mathrm{size}(c_1),\\ \mathrm{fee}(c_1) + \mathrm{diagram}\big(c', x - \mathrm{size}(c_1)\big) & \text{if } x > \mathrm{size}(c_1),\end{cases}$$
with rational division ($\cdot/0 = 0$). It is defined for every rational $x$, including negative $x$. For the empty list it is identically $0$. When every size is positive, writing $S_k = \sum_{i \le k}\mathrm{size}(c_i)$ and $F_k = \sum_{i \le k}\mathrm{fee}(c_i)$ (with $S_0 = F_0 = 0$) for $c = [c_1,\dots,c_n]$, $n \ge 1$, the recursion unfolds to: $\mathrm{diagram}(c,x) = \mathrm{fee}(c_1)\,x/\mathrm{size}(c_1)$ for all $x \le S_1$ (including negative $x$); $F_{k-1} + \mathrm{fee}(c_k)(x - S_{k-1})/\mathrm{size}(c_k)$ for $S_{k-1} \le x \le S_k$; and $F_n$ for $x \ge S_n$ — the piecewise-linear function through $(0,0), (S_1,F_1), \dots, (S_n,F_n)$, horizontal to the right. If a size is zero or negative the recursion still evaluates but need not have this shape (e.g. a chunk with $\mathrm{size}(c_1) < 0$ gives $\mathrm{diagram}(c, 0) = \mathrm{fee}(c_1) + \mathrm{diagram}(c', -\mathrm{size}(c_1))$; a chunk with size $0$ contributes a jump of $\mathrm{fee}(c_1)$ just after $x = 0$).

**diagramFee, diagramSize.** For $c = [c_1,\dots,c_n]$: $\mathrm{diagramFee}(c) = \sum_{i=1}^n \mathrm{fee}(c_i) \in \mathbb Z$ and $\mathrm{diagramSize}(c) = \sum_{i=1}^n \mathrm{size}(c_i) \in \mathbb Z$ (both $0$ for the empty list).

**SizesPos.** $\mathrm{SizesPos}(c)$ means $\mathrm{size}(c_i) > 0$ for every chunk $c_i$ in $c$ (vacuously true for the empty list). It says nothing about fees, which may be zero or negative.

**Dominates, BetterSomewhere, StrictlyBetter.** For chunk lists $c^0, c^1$:
- $\mathrm{Dominates}(c^0, c^1)$: for every rational $x \ge 0$, $\mathrm{diagram}(c^1, x) \le \mathrm{diagram}(c^0, x)$.
- $\mathrm{BetterSomewhere}(c^0, c^1)$: there is a rational $x \ge 0$ with $\mathrm{diagram}(c^1, x) < \mathrm{diagram}(c^0, x)$.
- $\mathrm{StrictlyBetter}(c^0, c^1)$: $\mathrm{Dominates}(c^0, c^1)$ and $\mathrm{BetterSomewhere}(c^0, c^1)$.

Only $x \ge 0$ is quantified over (negative $x$ is excluded; $x = 0$ is included), and $x$ ranges over all nonnegative rationals, including points beyond both total sizes.

**FeeRate and getFee** (from the imported replacement file). A *FeeRate* $r$ consists of natural numbers $\mathrm{fee}(r) \ge 0$ and $\mathrm{size}(r)$ with the built-in requirement $\mathrm{size}(r) > 0$. For $v \in \mathbb N$,
$$\mathrm{getFee}(r, v) = \big(\mathrm{fee}(r)\cdot v + (\mathrm{size}(r) - 1)\big) \mathbin{/} \mathrm{size}(r)$$
computed in the natural numbers with floor division ($\mathrm{size}(r) - 1 \ge 0$ since $\mathrm{size}(r) > 0$).

**Tx, Replacement, totalFee, PaysForRBF** (from the imported replacement file). A transaction $t$ is a pair of natural numbers $\mathrm{fee}(t) \ge 0$, $\mathrm{vsize}(t)$ with $\mathrm{vsize}(t) > 0$. A *Replacement* $R$ consists of a transaction $R.\mathrm{new}$, a finite multiset $R.\mathrm{evicted}$ of transactions, and a finite multiset $R.\mathrm{direct}$ of transactions with $R.\mathrm{direct} \le R.\mathrm{evicted}$ (sub-multiset, counting multiplicity); the multisets may be empty. $\mathrm{totalFee}(s) = \sum_{t \in s}\mathrm{fee}(t) \in \mathbb N$, summed with multiplicity ($0$ for the empty multiset). For a FeeRate $r$,
$$\mathrm{PaysForRBF}(r, R) \iff \mathrm{totalFee}(R.\mathrm{evicted}) \le \mathrm{fee}(R.\mathrm{new}) \ \text{ and }\ \mathrm{getFee}\big(r, \mathrm{vsize}(R.\mathrm{new})\big) \le \mathrm{fee}(R.\mathrm{new}) - \mathrm{totalFee}(R.\mathrm{evicted}),$$
where the subtraction is truncated subtraction of natural numbers (by the first conjunct it equals the ordinary difference).

