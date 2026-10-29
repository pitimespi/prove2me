# Read-back: `BitcoinBackbone.common_prefix`

**Statement.** Let $E$ be an execution of the backbone model, assumed *legal* (no mined-flag in round $0$; for $p<n$, $r\ge1$, $\mathrm{base}(p,r)$ is a valid chain; for $p<n$ every block of $\mathrm{base}(p,r)$ has round $<r$; for $p,q<n$ and every $r$, $|\mathcal{C}_q(r)|\le|\mathrm{base}(p,r+1)|$; for $j<Z_r$, $\mathrm{advParent}(r,j)$ is valid and all its blocks have round $\le r$). Let $\lambda\in\mathbb{N}$ and assume $E$ is *$\lambda$-typical*:

$$
\forall a,b\in\mathbb{N},\quad a+\lambda\le b \;\Longrightarrow\; \sum_{i=a}^{b} Z_i < \sum_{i=a+1}^{b-1} Y_i ,
$$

where $Y_i=1$ iff exactly one party index $p'<n$ has $\mathrm{mined}(p',i)=\mathtt{true}$, else $0$. Let $p_1, p_2$ be party indices with $p_1<n$ and $p_2<n$, and let $r_1\le r_2$ be rounds. Write $C_1 = \mathcal{C}_{p_1}(r_1)$ and $C_2 = \mathcal{C}_{p_2}(r_2)$ for the respective chains at the end of those rounds ($\mathcal{C}_p(0)=[\,]$; for $r\ge1$, $\mathrm{base}(p,r)$ with $\mathsf{honest}(p,r)$ appended iff $\mathrm{mined}(p,r)=\mathtt{true}$). Then

$$
\operatorname{take}\bigl(|C_1| \mathbin{\dot-} 2\lambda,\; C_1\bigr) \;\sqsubseteq\; C_2 ,
$$

i.e. the list consisting of the first $|C_1| \mathbin{\dot-} 2\lambda$ blocks of $C_1$ (positions $0,\dots,|C_1| \mathbin{\dot-} 2\lambda - 1$) is a *prefix* of $C_2$: there exists a list $L$ of blocks with $\operatorname{take}(|C_1| \mathbin{\dot-} 2\lambda, C_1) \mathbin{+\!\!+} L = C_2$.

**Truncated subtraction.** $\mathbin{\dot-}$ is natural-number subtraction, which returns $0$ instead of a negative value. Thus when $|C_1| \le 2\lambda$ the number of blocks kept is $0$, the kept list is $[\,]$, and the conclusion holds trivially since $[\,]$ is a prefix of every list. The statement is only informative when $|C_1| > 2\lambda$, in which case exactly the last $2\lambda$ blocks of $C_1$ are discarded and the remaining $|C_1|-2\lambda$ blocks, in order, must coincide with the first $|C_1|-2\lambda$ blocks of $C_2$.

**Other cases made explicit.** $p_1 = p_2$ and $r_1 = r_2$ are both permitted. The prefix relation is asymmetric: nothing is asserted about $C_2$ truncated being a prefix of $C_1$. $\lambda=0$ and $\lambda=1$ make the typicality hypothesis unsatisfiable (for $\lambda=0$, $a=b$ gives $Z_a<0$; for $\lambda=1$, $b=a+1$ gives an empty right-hand sum), so for those values the theorem is vacuous; typicality also forces $n\ge1$. If $r_1=0$ then $C_1=[\,]$ and the claim is trivial.
