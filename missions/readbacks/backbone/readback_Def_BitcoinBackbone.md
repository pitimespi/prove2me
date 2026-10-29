# Read-back: `Def_BitcoinBackbone.lean`

Everything below lives in a namespace called `BitcoinBackbone`; the file imports Mathlib and the block-validation preamble `Def_BitcoinBlockV2`, but none of the definitions in this file refer to anything from that preamble. One paragraph per definition, in file order.

---

**`Block` (inductive type).** A *block* is a value of one of exactly two shapes: an *honest block* $\mathsf{honest}(p, r)$ carrying two natural numbers $p$ (a party index) and $r$ (a round), or an *adversarial block* $\mathsf{adv}(r, j)$ carrying two natural numbers $r$ (a round) and $j$ (an index). Two blocks are equal exactly when they have the same shape and the same two numbers; in particular $\mathsf{honest}(p,r)$ and $\mathsf{adv}(r',j)$ are never equal, and $\mathsf{honest}(p,r) \ne \mathsf{honest}(p',r)$ whenever $p \ne p'$. Nothing restricts $p$, $r$ or $j$ at the level of the type: $\mathsf{honest}(10^9, 0)$ and $\mathsf{adv}(0, 10^9)$ are blocks. Equality of blocks is decidable. (An accompanying instance declares $\mathsf{adv}(0,0)$ as the default block value; it is used only as a junk value by out-of-range list indexing operations that need one.)

**`Block.round`.** The *round* of a block is a natural number read off from the block: $\operatorname{round}(\mathsf{honest}(p,r)) = r$ and $\operatorname{round}(\mathsf{adv}(r,j)) = r$. This is purely syntactic; a block "found in round $0$" is allowed by this definition.

**`Block.isHonest`.** A Boolean flag: $\operatorname{isHonest}(\mathsf{honest}(p,r)) = \mathtt{true}$ and $\operatorname{isHonest}(\mathsf{adv}(r,j)) = \mathtt{false}$. So "$B$ is adversarial" (as the theorem files write it, $\operatorname{isHonest}(B) = \mathtt{false}$) means exactly that $B$ has the shape $\mathsf{adv}(\cdot,\cdot)$.

**`Chain` (abbreviation).** A *chain* $C$ is simply a finite list of blocks, $C = [B_0, B_1, \dots, B_{\ell-1}]$, with $\ell = |C|$ its length; there is no genesis element in the list, no well-formedness condition, and repeated blocks are allowed. Throughout, positions are $0$-based: $C[i]$ is the $i$-th block counting from $0$, defined only for $i < |C|$. The empty list $[\,]$ is a chain. The documentation describes position $0$ as the oldest block, but this is a convention of the author, not something enforced by the type.

**`Chain.work`.** $\operatorname{work}(C) = |C|$, the length of the list $C$ as a natural number. (This definition is not used by any of the eight theorem statements.)

**`Chain.upTo`.** For a chain $C$ and a natural number $t$, $\operatorname{upTo}(C, t)$ is the longest *initial segment* of $C$ all of whose blocks have round $\le t$: scanning $C$ from position $0$, blocks are kept while $\operatorname{round}(B) \le t$, and the scan stops at the first block with $\operatorname{round}(B) > t$, discarding it and everything after it—even blocks further on whose round is $\le t$. If every block of $C$ has round $\le t$, then $\operatorname{upTo}(C,t) = C$; if $C[0]$ has round $> t$, or $C$ is empty, then $\operatorname{upTo}(C,t) = [\,]$. In general $\operatorname{upTo}(C,t)$ is a prefix of $C$ but it is *not* in general "the set of blocks of $C$ with round $\le t$" unless rounds are nondecreasing along $C$ (which nothing in the type guarantees).

**`Execution` (structure).** An *execution* $E$ is a 5-tuple of completely unconstrained data:

- $n \in \mathbb{N}$ (the number of honest parties; parties are the indices $0,\dots,n-1$; $n=0$ is allowed, in which case there are no parties);
- $\mathrm{mined} : \mathbb{N}\times\mathbb{N} \to \{\mathtt{true},\mathtt{false}\}$, a Boolean $\mathrm{mined}(p,r)$ for every party index $p$ and round $r$ (also defined for $p \ge n$, where its values are simply ignored by the counting definitions below);
- $Z : \mathbb{N} \to \mathbb{N}$, a natural number $Z_r$ for every round $r$ (including $r=0$; nothing forces $Z_0 = 0$);
- $\mathrm{base} : \mathbb{N}\times\mathbb{N}\to \text{Chain}$, a chain $\mathrm{base}(p,r)$ for every $p$ and $r$ (also for $r=0$ and for $p\ge n$);
- $\mathrm{advParent} : \mathbb{N}\times\mathbb{N}\to \text{Chain}$, a chain $\mathrm{advParent}(r,j)$ for every $r$ and $j$ (also for $j \ge Z_r$).

The structure itself imposes no relation between these fields; all constraints come from the separate predicate `Legal` below.

**`Execution.chain`.** For an execution $E$, a natural number $p$ (not required to satisfy $p<n$) and a round $r$, the chain $\mathcal{C}_p(r)$ ("the chain of $p$ at the end of round $r$") is defined by recursion on $r$:

$$
\mathcal{C}_p(0) = [\,],\qquad
\mathcal{C}_p(r+1) =
\begin{cases}
\mathrm{base}(p, r+1) \mathbin{+\!\!+} [\mathsf{honest}(p, r+1)] & \text{if } \mathrm{mined}(p, r+1) = \mathtt{true},\\
\mathrm{base}(p, r+1) & \text{otherwise.}
\end{cases}
$$

Here $\mathbin{+\!\!+}$ is list concatenation, so the honest block is appended at the *end* (highest position). Note that $\mathcal{C}_p(0)$ is the empty list regardless of $\mathrm{base}(p,0)$, and that for $r\ge1$ the definition does not depend on $\mathcal{C}_p(r-1)$ at all—only on $\mathrm{base}(p,r)$ and $\mathrm{mined}(p,r)$. Consequently $|\mathcal{C}_p(r)| = |\mathrm{base}(p,r)| + 1$ if $\mathrm{mined}(p,r)$ holds and $|\mathrm{base}(p,r)|$ otherwise, for $r \ge 1$.

**`Execution.honestCount`.** For a round $r$, $h_r = \#\{\,p \in \{0,\dots,n-1\} : \mathrm{mined}(p,r) = \mathtt{true}\,\}$, the number of party indices below $n$ for which the mined-flag is set in round $r$. Values of $\mathrm{mined}(p,r)$ with $p \ge n$ do not count. If $n = 0$ then $h_r = 0$ for every $r$. Note that this counts *parties*, which under this model is the same as counting honest blocks of round $r$ because each party has at most one flag per round.

**`Execution.X`.** $X_r = 1$ if $h_r > 0$ and $X_r = 0$ otherwise, a natural number (not a Boolean). So $X_r=1$ means: at least one party index $p<n$ has $\mathrm{mined}(p,r)=\mathtt{true}$.

**`Execution.Y`.** $Y_r = 1$ if $h_r = 1$ and $Y_r = 0$ otherwise, a natural number. So $Y_r = 1$ means: *exactly* one party index $p<n$ has $\mathrm{mined}(p,r)=\mathtt{true}$. In particular $Y_r = 0$ when two or more parties mined in round $r$ and when none did; if $n=0$ then $Y_r=0$ for all $r$.

**`Execution.Extends`.** For an execution $E$, a chain $P$ (the "parent") and a block $B$, the proposition $\operatorname{Extends}_E(P, B)$ is defined by cases on the shape of $B$:

- if $B = \mathsf{honest}(p,r)$: $\;p < n \;\wedge\; \mathrm{mined}(p,r) = \mathtt{true} \;\wedge\; P = \mathrm{base}(p,r)$ (equality of lists);
- if $B = \mathsf{adv}(r,j)$: $\;j < Z_r \;\wedge\; P = \mathrm{advParent}(r,j)$.

So an honest block "extends" exactly one chain, namely $\mathrm{base}(p,r)$, and only if the party is in range and the mined-flag is set; an adversarial block "extends" exactly $\mathrm{advParent}(r,j)$, and only if its index $j$ is below the adversarial count $Z_r$ of its round. Nothing here relates the round of $B$ to the rounds of blocks in $P$.

**`Execution.ValidChain`.** A chain $C = [B_0,\dots,B_{\ell-1}]$ is *valid* for $E$, written $\operatorname{Valid}_E(C)$, when for every position $i$ with $0 \le i < \ell$,

$$
\operatorname{Extends}_E\bigl([B_0,\dots,B_{i-1}],\; B_i\bigr),
$$

i.e. the block at position $i$ extends (in the sense just defined) exactly the list of the $i$ blocks before it (the first $i$ elements of $C$). Unfolded: for each $i<\ell$, either $B_i = \mathsf{honest}(p,r)$ with $p<n$, $\mathrm{mined}(p,r)=\mathtt{true}$ and $\mathrm{base}(p,r) = [B_0,\dots,B_{i-1}]$, or $B_i = \mathsf{adv}(r,j)$ with $j<Z_r$ and $\mathrm{advParent}(r,j) = [B_0,\dots,B_{i-1}]$. The empty chain is vacuously valid. For $i=0$ the condition says $B_0$ extends the empty list.

**`Execution.Legal` (structure of propositions).** An execution $E$ is *legal* when all six of the following hold:

1. *mined_zero*: for every $p \in \mathbb{N}$ (all $p$, not only $p<n$), $\mathrm{mined}(p,0) = \mathtt{false}$. Hence $h_0 = X_0 = Y_0 = 0$ and no honest block of the form $\mathsf{honest}(p,0)$ can appear in a valid chain. (Nothing analogous is required of $Z_0$ or of $\mathrm{advParent}(0,j)$.)
2. *base_valid*: for every $p$ and $r$ with $p<n$ and $1 \le r$, the chain $\mathrm{base}(p,r)$ is valid for $E$. (No requirement on $\mathrm{base}(p,0)$, nor on $\mathrm{base}(p,r)$ for $p \ge n$.)
3. *base_rounds*: for every $p<n$ and every $r$ (including $r=0$), every block $B$ occurring in the list $\mathrm{base}(p,r)$ satisfies $\operatorname{round}(B) < r$. For $r=0$ this forces $\mathrm{base}(p,0)=[\,]$ for $p<n$.
4. *base_length*: for all $p,q<n$ and every $r\in\mathbb{N}$ (including $r=0$), $|\mathcal{C}_q(r)| \le |\mathrm{base}(p, r+1)|$: the chain that party $p$ adopts in round $r+1$ is at least as long as the chain any party $q$ (including $q=p$) held at the end of round $r$. Only lengths are compared; no prefix or content relation is required.
5. *advParent_valid*: for every $r$ and every $j < Z_r$, the chain $\mathrm{advParent}(r,j)$ is valid for $E$.
6. *advParent_rounds*: for every $r$ and every $j<Z_r$, every block $B$ in $\mathrm{advParent}(r,j)$ satisfies $\operatorname{round}(B) \le r$ (non-strict, in contrast with item 3).

Nothing in `Legal` says that honest parties' chains are prefix-related, that $\mathrm{base}(p,r)$ is one of the previously broadcast chains, or anything about $\mathrm{mined}(p,r)$ for $r\ge1$.

**`Execution.Typical`.** For an execution $E$ and a natural number $\lambda$ (written `lam`), $\operatorname{Typical}_E(\lambda)$ is the statement: for all natural numbers $a, b$ with $a + \lambda \le b$,

$$
\sum_{i=a}^{b} Z_i \;<\; \sum_{i=a+1}^{b-1} Y_i ,
$$

where the left sum ranges over the closed interval $\{a, a+1, \dots, b\}$ and the right sum over the open interval $\{a+1,\dots,b-1\}$ (empty when $b \le a+1$); both are sums of natural numbers and the inequality is strict. Degenerate cases to note: when $\lambda = 0$, taking $b=a$ makes the right-hand sum empty (value $0$), so the condition demands $Z_a < 0$, which is impossible—hence $\operatorname{Typical}_E(0)$ is false for every $E$; likewise when $\lambda = 1$, taking $b = a+1$ gives an empty right-hand sum and the impossible demand $Z_a + Z_{a+1} < 0$, so $\operatorname{Typical}_E(1)$ is false for every $E$. If $n = 0$ then every $Y_i = 0$ and the condition is again impossible, so $\operatorname{Typical}_E(\lambda)$ forces $n \ge 1$. For $\lambda\ge2$ the condition requires, among other things, that every window of $\lambda+1$ consecutive rounds contain at least one round strictly inside it with $Y_i = 1$ (in particular infinitely many uniquely successful rounds), and that the adversarial counts over any window of length $\ge \lambda + 1$ be strictly fewer than the uniquely successful rounds strictly inside it. The window includes $a = 0$ and so also the round-$0$ value $Z_0$.

**`Execution.advBlocks`.** For rounds $a \le b$, $\operatorname{advBlocks}_E(a,b)$ is the finite set of blocks $\{\,\mathsf{adv}(s, j) : a \le s \le b,\; 0 \le j < Z_s\,\}$, obtained as the image of the pairs $(s,j)$ with $s\in\{a,\dots,b\}$, $j<Z_s$ under $(s,j)\mapsto \mathsf{adv}(s,j)$. If $a > b$ the set is empty. Since the map is injective, its cardinality is $\sum_{i=a}^{b} Z_i$. (This definition is not used by any of the eight theorem statements.)
