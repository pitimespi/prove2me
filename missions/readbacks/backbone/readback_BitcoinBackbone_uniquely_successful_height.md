# Read-back: `BitcoinBackbone.uniquely_successful_height`

**Statement.** Let $E$ be an execution of the backbone model, assumed *legal* (for every $p$, $\mathrm{mined}(p,0)=\mathtt{false}$; for $p<n$, $r\ge1$, $\mathrm{base}(p,r)$ is a valid chain; for $p<n$ every block of $\mathrm{base}(p,r)$ has round $<r$; for $p,q<n$ and all $r$, $|\mathcal{C}_q(r)|\le|\mathrm{base}(p,r+1)|$; for $j<Z_r$, $\mathrm{advParent}(r,j)$ is valid with all blocks of round $\le r$). Let $i\in\mathbb{N}$ be a round and $m\in\mathbb{N}$ a party index with:

- $m<n$;
- $\mathrm{mined}(m,i)=\mathtt{true}$;
- $Y_i=1$, i.e. the number of party indices $p'<n$ with $\mathrm{mined}(p',i)=\mathtt{true}$ is exactly $1$ (together with the previous item: $m$ is the unique such party).

Let $C=[C_0,\dots,C_{\ell-1}]$ be a chain that is *valid* for $E$: for every $k<\ell$, if $C_k=\mathsf{honest}(p',r')$ then $p'<n$, $\mathrm{mined}(p',r')=\mathtt{true}$ and $\mathrm{base}(p',r')=[C_0,\dots,C_{k-1}]$, while if $C_k=\mathsf{adv}(r',j)$ then $j<Z_{r'}$ and $\mathrm{advParent}(r',j)=[C_0,\dots,C_{k-1}]$. Let $t\in\mathbb{N}$ with $t<\ell$ and

$$
t \;=\; |\mathrm{base}(m,i)| ,
$$

the length of the chain party $m$ adopted in round $i$. Let $q, s\in\mathbb{N}$ and suppose the block of $C$ at $0$-based position $t$ is the honest block of party $q$ in round $s$:

$$
C_t \;=\; \mathsf{honest}(q,s).
$$

Then $q=m$ and $s=i$.

**What is and is not assumed.** Nothing is assumed about $q$ or $s$ beyond the equation $C_t=\mathsf{honest}(q,s)$ (validity of $C$ at position $t$ entails $q<n$, $\mathrm{mined}(q,s)=\mathtt{true}$ and $\mathrm{base}(q,s)=[C_0,\dots,C_{t-1}]$). $C$ is an arbitrary valid chain, not necessarily any party's chain. The round $s$ of the block is not assumed to be $i$; that is part of the conclusion. $t$ is a position (number of blocks below the block in question), and the hypothesis identifies it with the length of $\mathrm{base}(m,i)$, which under validity is the position at which $\mathsf{honest}(m,i)$ would sit in any valid chain containing it.

**Degenerate cases.** If $i=0$ the hypotheses are contradictory, since legality gives $\mathrm{mined}(m,0)=\mathtt{false}$ while $\mathrm{mined}(m,0)=\mathtt{true}$ is assumed; so effectively $i\ge1$. $n=0$ is excluded by $m<n$. If $t=0$ then $\mathrm{base}(m,i)=[\,]$ and the claim concerns $C_0$. No typicality hypothesis appears in this theorem.
