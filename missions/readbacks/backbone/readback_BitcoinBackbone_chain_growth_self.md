# Read-back: `BitcoinBackbone.chain_growth_self`

**Statement.** Let $E$ be an execution of the backbone model, assumed *legal* (no party has its mined-flag set in round $0$; for $p<n$, $r\ge1$ the chain $\mathrm{base}(p,r)$ is valid; for $p<n$ every block of $\mathrm{base}(p,r)$ has round $<r$; for all $p,q<n$ and all $r$, $|\mathcal{C}_q(r)| \le |\mathrm{base}(p,r+1)|$; for $j<Z_r$ the chain $\mathrm{advParent}(r,j)$ is valid with all blocks of round $\le r$). Let $p$ be a natural number with $p < n$, and let $r, s$ be natural numbers with $r \le s$ (non-strict). Then

$$
|\mathcal{C}_p(r)| \;+\; \sum_{i=r+1}^{s-1} X_i \;\le\; |\mathcal{C}_p(s)| ,
$$

where $\mathcal{C}_p(t)$ is party $p$'s chain at the end of round $t$ ($\mathcal{C}_p(0) = [\,]$; for $t\ge1$, $\mathrm{base}(p,t)$ followed by $\mathsf{honest}(p,t)$ if $\mathrm{mined}(p,t)=\mathtt{true}$, else $\mathrm{base}(p,t)$ alone), $|\cdot|$ is list length, and $X_i\in\{0,1\}$ is $1$ exactly when some party index $p'<n$ has $\mathrm{mined}(p',i)=\mathtt{true}$.

**Range of the sum.** The index $i$ runs over $\{r+1, \dots, s-1\}$, excluding both $r$ and $s$. This set is empty when $s \le r+1$; in particular, when $s = r$ the statement is the triviality $|\mathcal{C}_p(r)| \le |\mathcal{C}_p(r)|$, and when $s = r+1$ it is $|\mathcal{C}_p(r)| \le |\mathcal{C}_p(r+1)|$.

**Differences from `chain_growth`.** The same party $p$ appears on both sides (no second party $q$), and $r = s$ is permitted. Typicality is not assumed. $r=0$ is allowed ($|\mathcal{C}_p(0)|=0$). If $n=0$ the hypothesis $p<n$ cannot hold and the statement is vacuous.
