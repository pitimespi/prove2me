# Read-back: `BitcoinFeerateDiagram.diagram_at_zero`

**Statement.** For every finite list $c$ of FeeFracs (implicit argument) satisfying $\mathrm{SizesPos}(c)$ — every chunk has strictly positive size —
$$\mathrm{diagram}(c, 0) = 0 \quad (\text{in } \mathbb Q).$$

**Binders and edge cases.** Fees are arbitrary integers. The empty list satisfies the hypothesis vacuously and its diagram is $0$ everywhere. For a nonempty list with $\mathrm{size}(c_1) > 0$, the first case of the recursion applies at $x = 0$, giving $\mathrm{fee}(c_1)\cdot 0/\mathrm{size}(c_1)$. The hypothesis excludes lists containing a chunk of size $0$ or of negative size; for a first chunk of negative size the recursion would take the second branch at $x = 0$.

## Definitions used, unfolded

**FeeFrac.** A *FeeFrac* is a pair $X = (\mathrm{fee}(X), \mathrm{size}(X))$ of two arbitrary integers. Nothing constrains them: either component may be zero or negative, and no machine-word bounds are imposed. Addition and subtraction are componentwise,
$$X \pm Y = \big(\mathrm{fee}(X) \pm \mathrm{fee}(Y),\ \mathrm{size}(X) \pm \mathrm{size}(Y)\big),$$
and the zero FeeFrac is $(0,0)$. A *chunk list* is a finite list $c = [c_1, \dots, c_n]$ of FeeFracs; the empty list ($n = 0$) is allowed.

**diagram.** For a chunk list $c$ and $x \in \mathbb Q$, $\mathrm{diagram}(c, x) \in \mathbb Q$ is defined recursively:
$$\mathrm{diagram}([\,], x) = 0, \qquad \mathrm{diagram}(c_1 :: c', x) = \begin{cases} \mathrm{fee}(c_1)\cdot x / \mathrm{size}(c_1) & \text{if } x \le \mathrm{size}(c_1),\\ \mathrm{fee}(c_1) + \mathrm{diagram}\big(c', x - \mathrm{size}(c_1)\big) & \text{if } x > \mathrm{size}(c_1),\end{cases}$$
with rational division ($\cdot/0 = 0$). It is defined for every rational $x$, including negative $x$. For the empty list it is identically $0$. When every size is positive, writing $S_k = \sum_{i \le k}\mathrm{size}(c_i)$ and $F_k = \sum_{i \le k}\mathrm{fee}(c_i)$ (with $S_0 = F_0 = 0$) for $c = [c_1,\dots,c_n]$, $n \ge 1$, the recursion unfolds to: $\mathrm{diagram}(c,x) = \mathrm{fee}(c_1)\,x/\mathrm{size}(c_1)$ for all $x \le S_1$ (including negative $x$); $F_{k-1} + \mathrm{fee}(c_k)(x - S_{k-1})/\mathrm{size}(c_k)$ for $S_{k-1} \le x \le S_k$; and $F_n$ for $x \ge S_n$ — the piecewise-linear function through $(0,0), (S_1,F_1), \dots, (S_n,F_n)$, horizontal to the right. If a size is zero or negative the recursion still evaluates but need not have this shape (e.g. a chunk with $\mathrm{size}(c_1) < 0$ gives $\mathrm{diagram}(c, 0) = \mathrm{fee}(c_1) + \mathrm{diagram}(c', -\mathrm{size}(c_1))$; a chunk with size $0$ contributes a jump of $\mathrm{fee}(c_1)$ just after $x = 0$).

**SizesPos.** $\mathrm{SizesPos}(c)$ means $\mathrm{size}(c_i) > 0$ for every chunk $c_i$ in $c$ (vacuously true for the empty list). It says nothing about fees, which may be zero or negative.

