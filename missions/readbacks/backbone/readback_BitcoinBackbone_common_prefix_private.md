# Read-back: `BitcoinBackbone.common_prefix_private`

**Statement.** Let $E$ be an execution of the backbone model, assumed *legal* (no mined-flag in round $0$; for $p<n$, $r\ge1$, $\mathrm{base}(p,r)$ is a valid chain; for $p<n$ every block of $\mathrm{base}(p,r)$ has round $<r$; for $p,q<n$ and all $r$, $|\mathcal{C}_q(r)|\le|\mathrm{base}(p,r+1)|$; for $j<Z_r$, $\mathrm{advParent}(r,j)$ is valid with all blocks of round $\le r$). Let $\lambda\in\mathbb{N}$ and assume $E$ is *$\lambda$-typical*:

$$
\forall a,b\in\mathbb{N},\quad a+\lambda\le b \;\Longrightarrow\; \sum_{i=a}^{b} Z_i < \sum_{i=a+1}^{b-1} Y_i ,
$$

with $Y_i=1$ iff exactly one party index $p'<n$ has $\mathrm{mined}(p',i)=\mathtt{true}$, else $0$. Let $p<n$ be a party index and $r\in\mathbb{N}$ a round. Let $D = [D_0,\dots,D_{\ell-1}]$ be an arbitrary chain (list of blocks, $\ell=|D|$) satisfying:

1. **$D$ is valid for $E$**: for every position $k<\ell$, the block $D_k$ extends exactly the list $[D_0,\dots,D_{k-1}]$, meaning: if $D_k=\mathsf{honest}(p',r')$ then $p'<n$, $\mathrm{mined}(p',r')=\mathtt{true}$ and $\mathrm{base}(p',r') = [D_0,\dots,D_{k-1}]$; if $D_k=\mathsf{adv}(r',j)$ then $j<Z_{r'}$ and $\mathrm{advParent}(r',j)=[D_0,\dots,D_{k-1}]$.
2. **All rounds of $D$ are $\le r$**: every block $B$ in $D$ has $\operatorname{round}(B)\le r$.

Let $f, r_0\in\mathbb{N}$ with $f\le\ell$, and assume:

3. **Fork point** (a disjunction):
   - either $f=0$ and $r_0=0$;
   - or there exist a natural number $q$ and a proof that $f-1<\ell$ such that $0<f$ and $D_{f-1} = \mathsf{honest}(q, r_0)$ (the block at $0$-based position $f-1$ is the honest block of party $q$ in round $r_0$).
4. **Adversarial tail**: for every position $k<\ell$ with $f\le k$, the block $D_k$ is adversarial, i.e. $\operatorname{isHonest}(D_k)=\mathtt{false}$, equivalently $D_k$ has the shape $\mathsf{adv}(\cdot,\cdot)$.
5. **Window**: $r_0+\lambda\le r$.

Then

$$
|D| \;<\; |\mathcal{C}_p(r)| ,
$$

where $\mathcal{C}_p(r)$ is party $p$'s chain at the end of round $r$ ($[\,]$ if $r=0$; for $r\ge1$, $\mathrm{base}(p,r)$ with $\mathsf{honest}(p,r)$ appended iff $\mathrm{mined}(p,r)=\mathtt{true}$) and $|\cdot|$ is list length. The inequality is strict.

**Unpacking the fork disjunction.** The two disjuncts are mutually exclusive via the value of $f$: if $f=0$ the second disjunct fails (it requires $0<f$), so the first forces $r_0=0$; if $f>0$ the first disjunct fails, so the second must hold, and then $f-1<\ell$ is automatic from $0<f\le\ell$. So the hypothesis says: *either* $f=0$ and $r_0=0$ (in which case, by item 4, **every** block of $D$ is adversarial and item 5 reads $\lambda\le r$), *or* $f\ge1$, position $f-1$ of $D$ holds $\mathsf{honest}(q,r_0)$ for some $q$ (unconstrained in the hypothesis itself, but validity of $D$ at position $f-1$ entails $q<n$, $\mathrm{mined}(q,r_0)=\mathtt{true}$ and $\mathrm{base}(q,r_0)=[D_0,\dots,D_{f-2}]$), and all blocks at positions $f,\dots,\ell-1$ are adversarial. The blocks at positions $0,\dots,f-2$ are not constrained in honesty by hypotheses 3–4 (only by validity and the round bound).

**Edge cases.** $D$ need not be the chain of any party; it is any list satisfying 1–2. $f=\ell$ is allowed (empty adversarial tail; then $D$'s last block is $\mathsf{honest}(q,r_0)$ if $f>0$). If $D=[\,]$ then $f=0$, hence $r_0=0$, item 4 is vacuous, item 5 is $\lambda\le r$, and the conclusion asserts $0<|\mathcal{C}_p(r)|$, i.e. that $p$'s chain at round $r$ is non-empty. $0$- and $1$-typicality are unsatisfiable (for $\lambda=0$ take $a=b$; for $\lambda=1$ take $b=a+1$), so the theorem is vacuous for $\lambda\le1$; typicality also forces $n\ge1$. Legality's round-$0$ rule means an honest block with $r_0=0$ cannot occur in the valid chain $D$, so in the second disjunct $r_0\ge1$ is forced; in the first disjunct $r_0=0$ by fiat.
