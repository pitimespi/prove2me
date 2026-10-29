# Read-back: `BitcoinBackbone.common_prefix_rounds`

**Statement.** Let $E$ be an execution of the backbone model, assumed *legal* (no mined-flag in round $0$; for $p<n$, $r\ge1$, $\mathrm{base}(p,r)$ is valid; for $p<n$ every block of $\mathrm{base}(p,r)$ has round $<r$; for $p,q<n$ and all $r$, $|\mathcal{C}_q(r)|\le|\mathrm{base}(p,r+1)|$; for $j<Z_r$, $\mathrm{advParent}(r,j)$ is valid with all blocks of round $\le r$). Let $\lambda\in\mathbb{N}$ and assume $E$ is *$\lambda$-typical*:

$$
\forall a,b\in\mathbb{N},\quad a+\lambda\le b \;\Longrightarrow\; \sum_{i=a}^{b} Z_i < \sum_{i=a+1}^{b-1} Y_i ,
$$

with $Y_i=1$ iff exactly one party index $p'<n$ has $\mathrm{mined}(p',i)=\mathtt{true}$, else $0$. Let $p_1<n$, $p_2<n$ be party indices, $r_1\le r_2$ rounds, and $w\in\mathbb{N}$ a natural number with

$$
\lambda \;\le\; w \;\le\; r_1 .
$$

Let $C_1=\mathcal{C}_{p_1}(r_1)$ and $C_2=\mathcal{C}_{p_2}(r_2)$ be the chains at the end of the respective rounds ($\mathcal{C}_p(0)=[\,]$; for $r\ge1$, $\mathrm{base}(p,r)$ with $\mathsf{honest}(p,r)$ appended iff $\mathrm{mined}(p,r)=\mathtt{true}$). Then

$$
\operatorname{upTo}\bigl(C_1,\; r_1 - w\bigr) \;\sqsubseteq\; C_2 ,
$$

i.e. there is a list $L$ with $\operatorname{upTo}(C_1, r_1-w) \mathbin{+\!\!+} L = C_2$.

**Meaning of $\operatorname{upTo}$.** $\operatorname{upTo}(C_1, t)$ is the longest initial segment of $C_1$ in which every block has round $\le t$: scanning from position $0$, blocks are kept while $\operatorname{round}(B)\le t$ and the scan stops at the first block with $\operatorname{round}(B)>t$ (that block and everything after it, including any later blocks with round $\le t$, are discarded). Here $\operatorname{round}(\mathsf{honest}(p,r)) = \operatorname{round}(\mathsf{adv}(r,j)) = r$. Because $w\le r_1$ is assumed, $r_1 - w$ is an ordinary (non-truncated) subtraction.

**Cases made explicit.** When $w = r_1$ the cut-off is $r_1-w=0$, so only an initial run of blocks with round $\le 0$ (necessarily of the form $\mathsf{adv}(0,j)$, since legality forbids $\mathsf{honest}(\cdot,0)$ in a valid chain, though nothing forbids $Z_0>0$) is required to be a prefix of $C_2$. When $w=\lambda$ the cut-off is $r_1-\lambda$. $p_1=p_2$ and $r_1=r_2$ are permitted. If $r_1=0$ then $w=\lambda=0$ is forced by $\lambda\le w\le r_1$, but $0$-typicality is unsatisfiable, so that case is vacuous; $1$-typicality is also unsatisfiable, and typicality forces $n\ge1$. The prefix relation is one-directional.
