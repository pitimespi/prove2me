# Read-back: `BitcoinFeerateDiagram.diagram_concave`

**Statement.** Let $c = [c_1, \dots, c_n]$ be any finite list of FeeFracs such that

- $\mathrm{SizesPos}(c)$: $\mathrm{size}(c_i) > 0$ for every $i$; and
- $\mathrm{FeeratesNonIncreasing}(c)$: $\mathrm{fee}(c_{i+1})\cdot\mathrm{size}(c_i) \le \mathrm{fee}(c_i)\cdot\mathrm{size}(c_{i+1})$ for every pair of adjacent chunks.

Let $I = \{x \in \mathbb Q : 0 \le x \le \mathrm{diagramSize}(c)\}$, the closed interval of **rationals** from $0$ to the total size $\mathrm{diagramSize}(c) = \sum_i \mathrm{size}(c_i)$. Then the function $x \mapsto \mathrm{diagram}(c, x)$ is concave on $I$ over the scalar field $\mathbb Q$, which means:

1. $I$ is convex (as a subset of $\mathbb Q$), and
2. for all $x, y \in I$ and all rationals $\lambda, \mu \ge 0$ with $\lambda + \mu = 1$,
$$\lambda\,\mathrm{diagram}(c, x) + \mu\,\mathrm{diagram}(c, y) \le \mathrm{diagram}(c, \lambda x + \mu y).$$

**Binders and edge cases.** Fees are arbitrary integers (zero or negative allowed). Concavity is asserted only on $[0, \mathrm{diagramSize}(c)]$, not on the whole half-line $x \ge 0$ and not for negative $x$; only rational points and rational weights are involved. For the empty list, $\mathrm{diagramSize} = 0$ and $I = \{0\}$, so the claim reduces to $\mathrm{diagram}([\,], 0) \le \mathrm{diagram}([\,], 0)$. For a single chunk the sortedness hypothesis is vacuous. The sortedness hypothesis compares only adjacent chunks, by integer cross-multiplication.

## Definitions used, unfolded

**FeeFrac.** A *FeeFrac* is a pair $X = (\mathrm{fee}(X), \mathrm{size}(X))$ of two arbitrary integers. Nothing constrains them: either component may be zero or negative, and no machine-word bounds are imposed. Addition and subtraction are componentwise,
$$X \pm Y = \big(\mathrm{fee}(X) \pm \mathrm{fee}(Y),\ \mathrm{size}(X) \pm \mathrm{size}(Y)\big),$$
and the zero FeeFrac is $(0,0)$. A *chunk list* is a finite list $c = [c_1, \dots, c_n]$ of FeeFracs; the empty list ($n = 0$) is allowed.

**diagram.** For a chunk list $c$ and $x \in \mathbb Q$, $\mathrm{diagram}(c, x) \in \mathbb Q$ is defined recursively:
$$\mathrm{diagram}([\,], x) = 0, \qquad \mathrm{diagram}(c_1 :: c', x) = \begin{cases} \mathrm{fee}(c_1)\cdot x / \mathrm{size}(c_1) & \text{if } x \le \mathrm{size}(c_1),\\ \mathrm{fee}(c_1) + \mathrm{diagram}\big(c', x - \mathrm{size}(c_1)\big) & \text{if } x > \mathrm{size}(c_1),\end{cases}$$
with rational division ($\cdot/0 = 0$). It is defined for every rational $x$, including negative $x$. For the empty list it is identically $0$. When every size is positive, writing $S_k = \sum_{i \le k}\mathrm{size}(c_i)$ and $F_k = \sum_{i \le k}\mathrm{fee}(c_i)$ (with $S_0 = F_0 = 0$) for $c = [c_1,\dots,c_n]$, $n \ge 1$, the recursion unfolds to: $\mathrm{diagram}(c,x) = \mathrm{fee}(c_1)\,x/\mathrm{size}(c_1)$ for all $x \le S_1$ (including negative $x$); $F_{k-1} + \mathrm{fee}(c_k)(x - S_{k-1})/\mathrm{size}(c_k)$ for $S_{k-1} \le x \le S_k$; and $F_n$ for $x \ge S_n$ — the piecewise-linear function through $(0,0), (S_1,F_1), \dots, (S_n,F_n)$, horizontal to the right. If a size is zero or negative the recursion still evaluates but need not have this shape (e.g. a chunk with $\mathrm{size}(c_1) < 0$ gives $\mathrm{diagram}(c, 0) = \mathrm{fee}(c_1) + \mathrm{diagram}(c', -\mathrm{size}(c_1))$; a chunk with size $0$ contributes a jump of $\mathrm{fee}(c_1)$ just after $x = 0$).

**diagramFee, diagramSize.** For $c = [c_1,\dots,c_n]$: $\mathrm{diagramFee}(c) = \sum_{i=1}^n \mathrm{fee}(c_i) \in \mathbb Z$ and $\mathrm{diagramSize}(c) = \sum_{i=1}^n \mathrm{size}(c_i) \in \mathbb Z$ (both $0$ for the empty list).

**SizesPos.** $\mathrm{SizesPos}(c)$ means $\mathrm{size}(c_i) > 0$ for every chunk $c_i$ in $c$ (vacuously true for the empty list). It says nothing about fees, which may be zero or negative.

**FeeratesNonIncreasing.** $\mathrm{FeeratesNonIncreasing}(c)$ means: for every pair of *adjacent* chunks $c_i, c_{i+1}$,
$$\mathrm{fee}(c_{i+1})\cdot\mathrm{size}(c_i) \le \mathrm{fee}(c_i)\cdot\mathrm{size}(c_{i+1})$$
(integer cross-multiplication). It holds automatically for lists of length $0$ or $1$.

