# Read-back: `BitcoinUniqueness.heightScript_prefix`

**Statement.** For all natural numbers $a$ and $b$ such that
- $a < 2^{31}$ and
- $b < 2^{31}$,

if the byte string $\mathrm{heightScript}(a)$ is a prefix (initial segment, possibly the whole string) of the byte string $\mathrm{heightScript}(b)$, then $a = b$.

Formally:
$$\forall a, b \in \mathbb{N},\quad a < 2^{31} \ \wedge\ b < 2^{31} \ \wedge\ \mathrm{heightScript}(a) \sqsubseteq \mathrm{heightScript}(b) \ \Longrightarrow\ a = b,$$
where $x \sqsubseteq y$ means $y = x \mathbin{+\!\!+} z$ for some byte string $z$ (the Boolean prefix test returning true).

### What heightScript says

For a natural number $n$, $\mathrm{heightScript}(n)$ is the byte string
$$\mathrm{heightScript}(n) = \begin{cases} [\mathtt{0x00}] & n = 0,\\ [\mathtt{0x50} + n] & 1 \le n \le 16 \ (\text{a single byte in } \mathtt{0x51}..\mathtt{0x60}),\\ \mathrm{pushBytes}(\mathrm{serialize}(n)) & n \ge 17,\end{cases}$$
where, for $n \ge 17$ (so $n$ is positive and $\mathrm{serialize}$ takes its non-negative branch): $\mathrm{serialize}(n)$ is the little-endian base-256 digit string of $n$ with no trailing zero byte (the "magnitude"), followed by an extra byte $\mathtt{0x00}$ if and only if the top bit ($\mathtt{0x80}$) of the magnitude's last byte is set; and $\mathrm{pushBytes}(d)$, for a byte string $d$, is $[\,|d|\,] \mathbin{+\!\!+} d$ (one length byte then the data) when $|d| < 76$, is $[\mathtt{0x4c}, |d|] \mathbin{+\!\!+} d$ when $76 \le |d| \le 255$, is $[\mathtt{0x4d}] \mathbin{+\!\!+} (\text{2 little-endian bytes of } |d|) \mathbin{+\!\!+} d$ when $256 \le |d| \le 65535$, and is $[\mathtt{0x4e}] \mathbin{+\!\!+} (\text{4 little-endian bytes of } |d| \bmod 2^{32}) \mathbin{+\!\!+} d$ otherwise. For $17 \le n < 2^{31}$ the magnitude has between 1 and 4 bytes, so $\mathrm{serialize}(n)$ has between 1 and 5 bytes and $\mathrm{heightScript}(n)$ is one length byte (value 1 to 5) followed by those bytes.

### Edge cases and scope

- $a = 0$: $\mathrm{heightScript}(0) = [\mathtt{0x00}]$, a one-byte string; the claim then says no $b \ne 0$ below $2^{31}$ has a height script beginning with the byte $\mathtt{0x00}$.
- $1 \le a \le 16$: a single byte $\mathtt{0x50}+a$; for $a \ge 17$ the first byte is a length byte between $1$ and $5$.
- The prefix relation is reflexive, so $a = b$ trivially satisfies the hypothesis; the content is the converse direction only.
- The bounds $a, b < 2^{31}$ are hypotheses restricting the claim's scope; $\mathrm{heightScript}$ itself is defined for every natural number, and within the bounds the data pushed is at most 5 bytes, so only the first branch of $\mathrm{pushBytes}$ (one length byte followed by the data) is exercised. The theorem says nothing about $a$ or $b \ge 2^{31}$.
- Nothing about blocks, chain states, or validation appears in this statement; it is a statement about two byte strings computed from two natural numbers.
