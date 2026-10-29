# Read-back: `BitcoinTapSoundnessV2.commitment_soundness`

**Binders and hypotheses.** The theorem quantifies universally over:

- byte strings $q$ and $\mathit{internal32}$ (finite lists of 8-bit bytes; *no* length hypothesis is stated for either);
- a Boolean $\mathit{parity}$;
- a tree $T$ of type $\mathrm{TapTree}$ (built from $\mathrm{leaf}(v', s')$ with $v'$ a byte and $s'$ a byte string, and $\mathrm{branch}(l, r)$);
- a hypothesis $\mathit{hT}$: $\mathrm{HonestOutput}(q, \mathit{internal32}, \mathit{parity}, T)$, i.e. $\mathrm{checkTapTweak}(q, \mathit{internal32}, \mathrm{hash}(T), \mathit{parity}) = \mathrm{true}$;
- a byte string $\mathit{control}$ and a natural number $k$ (including $k = 0$);
- a hypothesis $\mathit{hc}$: $|\mathit{control}| = 33 + 32k$;
- a hypothesis $\mathit{hkey}$: $\mathrm{take}_{32}(\mathrm{drop}_1(\mathit{control})) = \mathit{internal32}$ (bytes 1 through 32 of $\mathit{control}$ equal $\mathit{internal32}$; together with $\mathit{hc}$ this forces $|\mathit{internal32}| = 32$);
- a hypothesis $\mathit{hpar}$: $\big[\mathit{control}[0] \bmod 2 = 1\big] = \mathit{parity}$ (the first byte of $\mathit{control}$ is odd iff $\mathit{parity}$; the default byte $0$ is used if $\mathit{control}$ is empty, which $\mathit{hc}$ excludes);
- a byte $v$ and a byte string $s$ (no constraint on $v$'s value or on $|s|$);
- a hypothesis $h$: $\mathrm{verifyTaprootCommitment}(\mathit{control}, q, \mathrm{tapleafHash}(v, s)) = \mathrm{true}$.

Write $L = \mathrm{tapleafHash}(v, s)$ and $R = \mathrm{taprootMerkleRoot}(\mathit{control}, L)$.

**Conclusion.** At least one of the following three alternatives holds (inclusive disjunction):

**(A)** $R = \mathrm{hash}(T)$, and moreover either
  - $\mathrm{scriptPathWitness}(T, \mathit{control}, v, s) = \mathrm{none}$ and $L \in \mathrm{leaves}(T)$; or
  - there exist byte strings $x, y$ with $\mathrm{scriptPathWitness}(T, \mathit{control}, v, s) = \mathrm{some}(x, y)$ and $\mathrm{Collides}(x, y)$.

**(B)** $R \neq \mathrm{hash}(T)$, and
$$\mathrm{Collides}\big(\mathrm{taggedPre}(\text{"TapTweak"}, \mathit{internal32} \| R),\; \mathrm{taggedPre}(\text{"TapTweak"}, \mathit{internal32} \| \mathrm{hash}(T))\big).$$

**(C)** $R \neq \mathrm{hash}(T)$, and there exists a pair of natural numbers $P$ such that $\mathrm{liftX}(\mathrm{beVal}(\mathit{internal32})) = \mathrm{some}(P)$ and
$$\mathrm{TweakCollision}\big(q, \mathit{parity}, P,\; \mathrm{tapTweakHash}(\mathit{internal32}, R),\; \mathrm{tapTweakHash}(\mathit{internal32}, \mathrm{hash}(T))\big).$$

**Unfoldings.** $\mathrm{SHA256}$ is the bundle's executable SHA-256 (MD padding, 64-byte-chunk compression from the standard IV, eight big-endian words out), total on byte strings. $\mathrm{ascii}(t)$ is the UTF-8 byte list of $t$. $\mathrm{tagged}(t, m) = \mathrm{SHA256}(\mathrm{SHA256}(\mathrm{ascii}(t)) \| \mathrm{SHA256}(\mathrm{ascii}(t)) \| m)$; $\mathrm{taggedPre}(t, m) = \mathrm{SHA256}(\mathrm{ascii}(t)) \| \mathrm{SHA256}(\mathrm{ascii}(t)) \| m$. $\mathrm{Collides}(x, y)$ means $x \neq y \wedge \mathrm{SHA256}(x) = \mathrm{SHA256}(y)$.

$\mathrm{writeCompactSize}(n)$: one byte $n$ if $n < 253$; else byte $253$ + 2 little-endian bytes if $n \le \mathtt{0xffff}$; else byte $254$ + 4 LE bytes if $n \le \mathtt{0xffffffff}$; else byte $255$ + 8 LE bytes. $\mathrm{leafMsg}(v, s) = [v] \| \mathrm{writeCompactSize}(|s|) \| s$ and $\mathrm{tapleafHash}(v, s) = \mathrm{tagged}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s))$.

$\mathrm{lexLt}$ is Boolean strict lexicographic order on byte strings (empty $<$ non-empty; compare first bytes, recurse on equal). $\mathrm{branchMsg}(a, b) = a \| b$ if $\mathrm{lexLt}(a, b)$ else $b \| a$; $\mathrm{tapbranchHash}(a, b) = \mathrm{tagged}(\text{"TapBranch"}, \mathrm{branchMsg}(a, b))$.

$\mathrm{hash}(\mathrm{leaf}(v', s')) = \mathrm{tapleafHash}(v', s')$; $\mathrm{hash}(\mathrm{branch}(l, r)) = \mathrm{tapbranchHash}(\mathrm{hash}(l), \mathrm{hash}(r))$. $\mathrm{leaves}(\mathrm{leaf}(v', s')) = [\mathrm{tapleafHash}(v', s')]$; $\mathrm{leaves}(\mathrm{branch}(l, r)) = \mathrm{leaves}(l) \| \mathrm{leaves}(r)$; $L \in \mathrm{leaves}(T)$ is list membership of the hash $L$ (not of the pair $(v, s)$).

$\mathrm{controlNodes}(\mathit{control})$: with $m = \lfloor(|\mathit{control}| \dot- 33)/32\rfloor$ ($\dot-$ truncated subtraction), the list of $m$ consecutive 32-byte chunks of $\mathit{control}$ after its first 33 bytes. Under $\mathit{hc}$, $m = k$ and the chunks are exactly the $k$ trailing 32-byte blocks, $n_1, \dots, n_k$. $\mathrm{taprootMerkleRoot}(\mathit{control}, L)$ is the left fold $h_0 = L$, $h_i = \mathrm{tapbranchHash}(h_{i-1}, n_i)$, result $h_k$; for $k = 0$, $R = L$.

$\mathrm{tapTweakHash}(i, r) = \mathrm{tagged}(\text{"TapTweak"}, i \| r)$. $\mathrm{beVal}(b)$ is the big-endian natural-number value of $b$. With $p = 2^{256} - 2^{32} - 977$: $\mathrm{liftX}(x)$ is $\mathrm{none}$ if $x \ge p$; else with $y = (x^3+7)^{(p+1)/4} \bmod p$, it is $\mathrm{some}(x, y')$ with $y'$ the even one of $y$ and $(p - y) \bmod p$ if $y^2 \equiv x^3 + 7 \pmod p$, and $\mathrm{none}$ otherwise.

$\mathrm{xonlyTweakAddCheck}(\mathit{out}, \mathit{par}, P, \mathit{tw})$: let $t = \mathrm{beVal}(\mathit{tw})$; false if $t \ge n$ ($n$ the secp256k1 order constant); else $Q = \mathrm{padd}(\mathrm{some}(P), \mathrm{pmul}(t, G))$ with $G$ the base-point constant, $\mathrm{pmul}$ double-and-add with 257 fuel from infinity (so $\mathrm{pmul}(0, G)$ is infinity), and $\mathrm{padd}$ affine addition mod $p$ with infinity as identity, infinity on $x_1 \equiv x_2$ with $y_1 + y_2 \equiv 0$, doubling formula otherwise on equal $x$, chord formula on distinct $x$, field inverses by Fermat exponentiation ($0 \mapsto 0$); false if $Q$ is infinity; else with $Q = (q_x, q_y)$ the value is $[\mathrm{be32}(q_x) = \mathit{out}] \wedge [(q_y \bmod 2 = 1) = \mathit{par}]$, $\mathrm{be32}$ being 32-byte big-endian encoding mod $2^{256}$.

$\mathrm{checkTapTweak}(q, i, r, \mathit{par})$: false if $\mathrm{liftX}(\mathrm{beVal}(i)) = \mathrm{none}$; else, with $\mathrm{some}(P)$, $\mathrm{xonlyTweakAddCheck}(q, \mathit{par}, P, \mathrm{tapTweakHash}(i, r))$. $\mathrm{verifyTaprootCommitment}(c, \mathit{prog}, \ell) = \mathrm{checkTapTweak}\big(\mathit{prog}, \mathrm{take}_{32}(\mathrm{drop}_1(c)), \mathrm{taprootMerkleRoot}(c, \ell), [c[0] \bmod 2 = 1]\big)$ (default byte $0$ for $c[0]$ when $c$ is empty). So, given $\mathit{hkey}$ and $\mathit{hpar}$, hypothesis $h$ unfolds to $\mathrm{checkTapTweak}(q, \mathit{internal32}, R, \mathit{parity}) = \mathrm{true}$, and $\mathit{hT}$ to $\mathrm{checkTapTweak}(q, \mathit{internal32}, \mathrm{hash}(T), \mathit{parity}) = \mathrm{true}$; both therefore require $\mathrm{liftX}(\mathrm{beVal}(\mathit{internal32}))$ to be $\mathrm{some}(P)$ for the same $P$, $\mathrm{beVal}$ of each tweak hash to be $< n$, and the resulting point to be non-infinite with abscissa encoding $q$ and the stated parity.

$\mathrm{TweakCollision}(q, \mathit{par}, P, t_1, t_2)$ is $t_1 \neq t_2 \wedge |t_1| = 32 \wedge |t_2| = 32 \wedge \mathrm{xonlyTweakAddCheck}(q, \mathit{par}, P, t_1) = \mathrm{true} \wedge \mathrm{xonlyTweakAddCheck}(q, \mathit{par}, P, t_2) = \mathrm{true}$.

$\mathrm{walk}(T, \mathit{path}, h)$ returns either a tree ($\mathrm{inl}$) or a pair of byte strings ($\mathrm{inr}$): $\mathrm{walk}(T, [], h) = \mathrm{inl}(T)$; for $n :: \mathit{rest}$, let $W = \mathrm{walk}(T, \mathit{rest}, \mathrm{tapbranchHash}(h, n))$; if $W = \mathrm{inr}(c)$ return $\mathrm{inr}(c)$; if $W = \mathrm{inl}(\mathrm{leaf}(v', s'))$ return $\mathrm{inr}(\mathrm{taggedPre}(\text{"TapLeaf"}, \mathrm{leafMsg}(v', s')), \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(h, n)))$; if $W = \mathrm{inl}(\mathrm{branch}(l, r))$ return $\mathrm{inl}(l)$ if $h = \mathrm{hash}(l)$, else $\mathrm{inl}(r)$ if $h = \mathrm{hash}(r)$, else $\mathrm{inr}(\mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(\mathrm{hash}(l), \mathrm{hash}(r))), \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(h, n)))$. The path is consumed so that the tree is descended from the root while the list is read from its last element; no length or root check is performed inside $\mathrm{walk}$.

$\mathrm{scriptPathWitness}(T, \mathit{control}, v, s)$: from $W = \mathrm{walk}(T, \mathrm{controlNodes}(\mathit{control}), L)$: $\mathrm{inr}(c) \mapsto \mathrm{some}(c)$; $\mathrm{inl}(\mathrm{leaf}(\cdot, \cdot)) \mapsto \mathrm{none}$ (the leaf's contents are not compared with $v, s$); $\mathrm{inl}(\mathrm{branch}(l, r)) \mapsto \mathrm{some}(\mathrm{taggedPre}(\text{"TapLeaf"}, \mathrm{leafMsg}(v, s)), \mathrm{taggedPre}(\text{"TapBranch"}, \mathrm{branchMsg}(\mathrm{hash}(l), \mathrm{hash}(r))))$.

**Edge cases and what is silently included.** $k$ appears only in $\mathit{hc}$; $k = 0$ (a 33-byte control block, empty path, $R = L$) is allowed, and so is any $k$, with no upper bound such as 128. $v$ is an arbitrary byte: nothing restricts the leaf version or ties $v$ to the first byte of $\mathit{control}$. Neither $q$ nor $s$ carries a length hypothesis; $|\mathit{internal32}| = 32$ follows from $\mathit{hkey}$ and $\mathit{hc}$ but is not stated directly. The three alternatives are not asserted to be exclusive. In (A), both sub-alternatives may be true simultaneously in principle; the first sub-alternative asserts membership of the *hash* $L$ in $\mathrm{leaves}(T)$, which is a list of hashes and may contain repeats. In (B) and (C) the colliding objects are explicit expressions in $\mathit{internal32}$, $R$, $\mathrm{hash}(T)$, $q$ and $\mathit{parity}$: (B) names two $(64 + 64)$-byte strings and asserts they differ and have the same SHA-256; (C) names two 32-byte tweak hashes and asserts they differ, both have length 32, and both pass $\mathrm{xonlyTweakAddCheck}$ against $q$, $\mathit{parity}$ and the lifted point $P$ of $\mathit{internal32}$. Alternative (A) does not itself assert any collision when its first sub-alternative is used. The hypotheses $\mathit{hT}$ and $h$ are both Boolean equalities to $\mathrm{true}$; if either computation yields false for every choice of inputs in some situation (e.g. $\mathrm{liftX}$ failing on $\mathit{internal32}$), the theorem is vacuous there.
