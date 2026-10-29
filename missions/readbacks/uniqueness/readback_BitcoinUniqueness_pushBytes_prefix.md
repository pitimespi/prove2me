# Read-back: `BitcoinUniqueness.pushBytes_prefix`

**Statement.** For all byte strings $d$ and $d'$ (finite lists of 8-bit words) such that
- $|d| < 2^{32}$ and
- $|d'| < 2^{32}$,

if $\mathrm{pushBytes}(d)$ is a prefix (initial segment, possibly the whole string) of $\mathrm{pushBytes}(d')$, then $d = d'$.

Formally:
$$\forall d, d' \in \mathrm{Bytes},\quad |d| < 2^{32} \ \wedge\ |d'| < 2^{32} \ \wedge\ \mathrm{pushBytes}(d) \sqsubseteq \mathrm{pushBytes}(d') \ \Longrightarrow\ d = d',$$
where $x \sqsubseteq y$ means $y = x \mathbin{+\!\!+} z$ for some byte string $z$.

### What pushBytes says

For a byte string $d$ with length $\ell = |d|$:
$$\mathrm{pushBytes}(d) = \begin{cases} [\ell] \mathbin{+\!\!+} d & \ell < 76 \ (\mathtt{0x4c}),\\ [\mathtt{0x4c},\ \ell] \mathbin{+\!\!+} d & 76 \le \ell \le 255,\\ [\mathtt{0x4d}] \mathbin{+\!\!+} \mathrm{le}_2(\ell) \mathbin{+\!\!+} d & 256 \le \ell \le 65535,\\ [\mathtt{0x4e}] \mathbin{+\!\!+} \mathrm{le}_4(\ell) \mathbin{+\!\!+} d & \ell \ge 65536,\end{cases}$$
where $[\ell]$ and $[\mathtt{0x4c}, \ell]$ write $\ell$ as one byte (reduced modulo 256, which is lossless in those branches), and $\mathrm{le}_k(\ell)$ is the $k$-byte little-endian encoding of $\ell \bmod 2^{8k}$. In the last branch the length is encoded modulo $2^{32}$; the hypotheses $|d|, |d'| < 2^{32}$ make that encoding lossless.

### Edge cases and scope

- $d = [\,]$: $\mathrm{pushBytes}([\,]) = [\mathtt{0x00}]$; the claim then says no non-empty $d'$ (of length below $2^{32}$) has a push beginning with the byte $\mathtt{0x00}$.
- The prefix relation is reflexive, so $d = d'$ trivially satisfies the hypothesis; the content is the converse direction only.
- The two length bounds are hypotheses on the claim's scope; $\mathrm{pushBytes}$ is defined for every byte string. The theorem says nothing about strings of length $\ge 2^{32}$.
- The statement concerns only the canonical push encoding of two byte strings; no script parsing, block or chain state is involved.
