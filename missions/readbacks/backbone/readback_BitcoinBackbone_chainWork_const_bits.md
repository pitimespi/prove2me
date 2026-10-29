# Read-back: `BitcoinBackbone.chainWork_const_bits`

This declaration is stated inside the `BitcoinBackbone` namespace but refers only to objects from the block-validation preamble (`BitcoinBlockV2`, `BitcoinSer`, `BitcoinPow`); none of the backbone definitions (executions, chains of abstract blocks, typicality, …) occur in it.

**Statement.** Let $S$ be a *chain state*: a pair $S=(\mathit{headers}, \mathit{utxo})$ where $\mathit{headers}=[h_0,\dots,h_{\ell-1}]$ is a finite list of block headers and $\mathit{utxo}$ is a ledger (unconstrained here and not used by the statement). A header $h$ is a record with fields $\mathit{version}\in\mathbb{Z}$, $\mathit{prevBlock}$ and $\mathit{merkleRoot}$ (byte strings), $\mathit{time}\in\mathbb{N}$, $\mathit{bits}\in\mathbb{N}$ (an unbounded natural number, not a 32-bit word) and $\mathit{nonce}\in\mathbb{N}$. Let $\mathit{bits}\in\mathbb{N}$ and assume every header in the list has that bits-field:

$$
\forall h\in\mathit{headers},\quad h.\mathit{bits}=\mathit{bits}.
$$

Then

$$
\operatorname{chainWork}(S) \;=\; \ell\cdot\operatorname{blockProof}(\mathit{bits}),
$$

where $\ell=|\mathit{headers}|$ and multiplication is on natural numbers.

**Unfolding $\operatorname{chainWork}$.** $\operatorname{chainWork}(S)=\sum_{k=0}^{\ell-1}\operatorname{blockProof}(h_k.\mathit{bits})$, the natural-number sum of $\operatorname{blockProof}$ applied to each header's bits-field, in list order; the sum of the empty list is $0$.

**Unfolding $\operatorname{blockProof}(b)$ for $b\in\mathbb{N}$.** First $b$ is reduced to a 32-bit word $c = b \bmod 2^{32}$. From $c$ one computes $\mathit{nSize}=\lfloor c/2^{24}\rfloor$ (the top byte) and $\mathit{nWord}=c \wedge \mathtt{0x007fffff}$ (the low 23 bits), and the candidate target

$$
t=\begin{cases}\lfloor \mathit{nWord}/2^{8(3-\mathit{nSize})}\rfloor & \text{if } \mathit{nSize}\le3,\\[2pt] \bigl(\mathit{nWord}\cdot 2^{8(\mathit{nSize}-3)}\bigr)\bmod 2^{256} & \text{if } \mathit{nSize}>3.\end{cases}
$$

The target is *rejected* (the derivation returns "none") if any of the following holds: (i) $\mathit{nWord}\ne0$ and bit $\mathtt{0x00800000}$ of $c$ is set ("negative"); (ii) $t=0$; (iii) $\mathit{nWord}\ne0$ and ($\mathit{nSize}>34$, or $\mathit{nWord}>\mathtt{0xff}$ and $\mathit{nSize}>33$, or $\mathit{nWord}>\mathtt{0xffff}$ and $\mathit{nSize}>32$) ("overflow"); (iv) $t>2^{224}-1$. Then

$$
\operatorname{blockProof}(b)=\begin{cases}0 & \text{if the target is rejected},\\[2pt] \left\lfloor\dfrac{2^{256}-1-t}{t+1}\right\rfloor+1 & \text{otherwise, with } t \text{ the derived target}.\end{cases}
$$

Since an accepted $t$ satisfies $1\le t\le 2^{224}-1$, the subtraction $2^{256}-1-t$ is an ordinary one and the division is integer (floor) division.

**Edge cases.** If $\mathit{headers}=[\,]$ the hypothesis is vacuous and both sides are $0$. The hypothesis says nothing about the headers beyond their bits-field: they need not be chained by $\mathit{prevBlock}$, need not begin with the genesis header, need not satisfy proof-of-work, and the common value $\mathit{bits}$ need not encode an acceptable target (if it does not, both sides are $0$). Two values of $\mathit{bits}$ that agree modulo $2^{32}$ give the same $\operatorname{blockProof}$, but the hypothesis demands literal equality of the natural numbers $h.\mathit{bits}=\mathit{bits}$. Equality in the conclusion is equality of natural numbers.
