# Read-back: `BitcoinBackbone.chain_quality`

**Statement.** Let $E$ be an execution of the backbone model, assumed *legal* (no mined-flag in round $0$; for $p<n$, $r\ge1$, $\mathrm{base}(p,r)$ is a valid chain; for $p<n$ all blocks of $\mathrm{base}(p,r)$ have round $<r$; for $p,q<n$ and all $r$, $|\mathcal{C}_q(r)|\le|\mathrm{base}(p,r+1)|$; for $j<Z_r$, $\mathrm{advParent}(r,j)$ is valid with all blocks of round $\le r$). Let $\lambda\in\mathbb{N}$ and assume $E$ is *$\lambda$-typical*:

$$
\forall a, b \in \mathbb{N},\quad a+\lambda \le b \;\Longrightarrow\; \sum_{i=a}^{b} Z_i < \sum_{i=a+1}^{b-1} Y_i ,
$$

with $Y_i = 1$ exactly when exactly one party index $p'<n$ has $\mathrm{mined}(p',i)=\mathtt{true}$ (else $0$). Let $p<n$, let $r\in\mathbb{N}$ be a round and $u\in\mathbb{N}$ a position, and assume

$$
u + \lambda \;\le\; |\mathcal{C}_p(r)| ,
$$

where $\mathcal{C}_p(r)$ is party $p$'s chain at the end of round $r$ ($[\,]$ for $r=0$; otherwise $\mathrm{base}(p,r)$ with $\mathsf{honest}(p,r)$ appended iff $\mathrm{mined}(p,r)=\mathtt{true}$). Then there exists a block $B$ occurring in the list

$$
W \;=\; \bigl[\,\mathcal{C}_p(r)[u],\; \mathcal{C}_p(r)[u+1],\;\dots,\;\mathcal{C}_p(r)[u+\lambda-1]\,\bigr]
$$

(the chain with its first $u$ elements removed, then truncated to its first $\lambda$ elements) such that $B$ has the shape $\mathsf{honest}(\cdot,\cdot)$, i.e. $\operatorname{isHonest}(B) = \mathtt{true}$.

**Indexing and window.** Positions are $0$-based, so $W$ consists of the blocks at positions $u, u+1, \dots, u+\lambda-1$. In general "drop $u$ then take $\lambda$" returns fewer than $\lambda$ blocks when the list is too short (dropping past the end yields $[\,]$, taking past the end yields what remains), but under the hypothesis $u+\lambda\le|\mathcal{C}_p(r)|$ the window $W$ has exactly $\lambda$ elements. The conclusion is an existence claim: at least one honest block in $W$, with no lower bound on how many.

**Degenerate cases.** If $\lambda = 0$ then $W = [\,]$ and the conclusion is false; however $0$-typicality is unsatisfiable (taking $a=b$ gives the impossible $Z_a < 0$), so this case is vacuous. Likewise $1$-typicality is unsatisfiable ($b=a+1$ gives an empty right-hand sum). Typicality also forces $n\ge1$ (if $n=0$ every $Y_i=0$). If $r=0$ then $\mathcal{C}_p(0)=[\,]$ and $u+\lambda\le 0$ forces $u=\lambda=0$, again vacuous. The window may start anywhere ($u$ is unconstrained except by $u+\lambda\le|\mathcal{C}_p(r)|$), including $u=0$.
