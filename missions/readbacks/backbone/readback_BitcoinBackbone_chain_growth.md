# Read-back: `BitcoinBackbone.chain_growth`

**Statement.** Let $E$ be an execution of the backbone model (a 5-tuple $(n, \mathrm{mined}, Z, \mathrm{base}, \mathrm{advParent})$, see the definition read-back), and assume $E$ is *legal* (the six conditions: no party has its mined-flag set in round $0$; for $p<n$ and $r\ge1$ the chain $\mathrm{base}(p,r)$ is valid; for $p<n$ every block of $\mathrm{base}(p,r)$ has round $<r$; for all $p,q<n$ and all $r$, $|\mathcal{C}_q(r)| \le |\mathrm{base}(p,r+1)|$; for $j<Z_r$ the chain $\mathrm{advParent}(r,j)$ is valid and all its blocks have round $\le r$). Let $p, q$ be natural numbers with $p < n$ and $q < n$ (so $n \ge 1$ is forced), and let $r, s$ be natural numbers with $r < s$ (strict). Then

$$
|\mathcal{C}_p(r)| \;+\; \sum_{i=r+1}^{s-1} X_i \;\le\; |\mathcal{C}_q(s)| .
$$

**Meaning of the symbols.**

- $\mathcal{C}_p(r)$ is party $p$'s chain at the end of round $r$: $\mathcal{C}_p(0) = [\,]$, and for $r \ge 1$ it is $\mathrm{base}(p,r)$ with the block $\mathsf{honest}(p,r)$ appended if $\mathrm{mined}(p,r) = \mathtt{true}$, and $\mathrm{base}(p,r)$ itself otherwise. $|\cdot|$ is list length.
- $X_i \in \{0,1\}$ equals $1$ exactly when at least one party index $p' < n$ has $\mathrm{mined}(p', i) = \mathtt{true}$, and $0$ otherwise.
- The sum runs over the half-open integer interval $\{r+1, \dots, s-1\}$: it excludes round $r$ and round $s$ themselves. When $s = r+1$ the interval is empty and the sum is $0$, so the statement reduces to $|\mathcal{C}_p(r)| \le |\mathcal{C}_q(r+1)|$.

**Edge cases made explicit.** $p = q$ is allowed. $r = 0$ is allowed, in which case $|\mathcal{C}_p(0)| = 0$ and the claim is $\sum_{i=1}^{s-1} X_i \le |\mathcal{C}_q(s)|$. The hypothesis $\lambda$-typicality does **not** appear in this theorem; only legality is assumed. Nothing is claimed about prefix relations between the two chains, only about their lengths. If $n = 0$ the hypotheses $p<n$, $q<n$ are unsatisfiable and the statement is vacuous.
