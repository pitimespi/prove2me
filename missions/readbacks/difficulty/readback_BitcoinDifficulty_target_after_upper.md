# Read-back: theorem `BitcoinDifficulty.target_after_upper`

## Statement

**Binders (universally quantified).**

- $c$, a compact word (a 32-bit word, named `bits`);
- $P$, a finite list of pairs of integers $(\ell_i, f_i)$ (named `periods`), quantified inside the statement after the hypothesis on $c$; possibly empty; entries arbitrary and unrelated.

**Hypothesis.**

- (hb) $D(c) \le L = 2^{224} - 1$.

**Conclusion.** For every such list $P$, writing $k = |P|$ for its length,

$$
D\big( A(c, P) \big) \;\le\; 4^{k} \cdot D(c),
$$

a non-strict inequality between natural numbers, with $4^k \cdot D(c)$ an ordinary product (no reduction modulo $2^{256}$ and no cap at $L$ on the right-hand side).

## Definitions used

**Constants (from the imported proof-of-work definitions).**

- $W = 2^{256}$ (the modulus called `width`).
- $L = 2^{224} - 1$ (the value called `powLimit`).
- $T = 14 \cdot 24 \cdot 60 \cdot 60 = 1{,}209{,}600$ (the value called `targetTimespan`); hence $\lfloor T/4 \rfloor = 302{,}400$ and $4T = 4{,}838{,}400$.

**Decoding a compact word, $D(c)$ (the function called `setCompact`).** A *compact word* $c$ is a 32-bit word, i.e. an integer with $0 \le c < 2^{32}$. Put

- $e(c) = \lfloor c / 2^{24} \rfloor$, the top byte of $c$, an integer in $[0, 255]$;
- $m(c) = c \bmod 2^{23}$, the low 23 bits of $c$ (bit 23, worth $2^{23}$, and the top byte are discarded).

Then $D(c)$ is the natural number

$$
D(c) =
\begin{cases}
\left\lfloor m(c) \,/\, 2^{\,8(3 - e(c))} \right\rfloor & \text{if } e(c) \le 3,\\[4pt]
\left( m(c) \cdot 2^{\,8(e(c) - 3)} \right) \bmod 2^{256} & \text{if } e(c) \ge 4.
\end{cases}
$$

Consequences of this definition that the quantifiers below silently include: $D(c) < 2^{256}$ always; $D(c) = 0$ whenever $m(c) = 0$, whenever $e(c) = 0$, and whenever $e(c) \ge 35$ (the shift then exceeds 256 bits and the reduction modulo $2^{256}$ leaves $0$); for $e(c) = 33$ or $34$ only the low 16 or low 8 bits of $m(c)$ survive the reduction; a word whose bit 23 ("sign" bit) is set decodes to the same value as the word with that bit cleared. $D$ never consults the overflow or sign conditions of the original code; it is a total function on all $2^{32}$ words.

**Encoding a natural number, $E(v)$ (the function called `getCompact`).** For a natural number $v$ let $b(v)$ be its bit length ($b(0) = 0$, and $b(v) = \lfloor \log_2 v \rfloor + 1$ for $v \ge 1$) and let $s = \lfloor (b(v) + 7)/8 \rfloor$ (the number of bytes of $v$). Put

$$
n =
\begin{cases}
\left( (v \bmod 2^{64}) \cdot 2^{\,8(3-s)} \right) \bmod 2^{32} & \text{if } s \le 3,\\[4pt]
\left( \left\lfloor v / 2^{\,8(s-3)} \right\rfloor \bmod 2^{64} \right) \bmod 2^{32} & \text{if } s \ge 4.
\end{cases}
$$

If bit 23 of $n$ is set (i.e. $n \wedge 2^{23} \neq 0$, bitwise and), let $n' = \lfloor n / 2^{8} \rfloor$ and $s' = s + 1$; otherwise $n' = n$ and $s' = s$. Then $E(v)$ is the 32-bit word $\left( n' \;\mathrm{OR}\; (s' \cdot 2^{24}) \right) \bmod 2^{32}$ (bitwise or, then reduction modulo $2^{32}$).

Consequences: for every $v < 2^{256}$ one has $s \le 32$ and $n < 2^{24}$, so the reductions modulo $2^{64}$ and $2^{32}$ change nothing and the bitwise or is a plain sum $n' + s' \cdot 2^{24}$; the word $E(v)$ then has top byte $s'$ and low 23 bits $n'$ (bit 23 of $n'$ is clear). Composing with $D$: for $v < 2^{256}$, $D(E(v))$ equals $v$ with its lowest $8(s-3)$ bits set to zero (lowest $8(s-2)$ bits when the bit-23 adjustment fired; nothing zeroed when $s \le 3$ and no adjustment), so in particular $D(E(v)) \le v$, and $D(E(0)) = 0$.

**Clamping a timespan, $\kappa(a)$ (the function called `clampTimespan`).** For an integer $a$ (positive, zero or negative),

$$
\kappa(a) =
\begin{cases}
302{,}400 & \text{if } a < 302{,}400,\\
4{,}838{,}400 & \text{if } a > 4{,}838{,}400,\\
a & \text{otherwise.}
\end{cases}
$$

$\kappa(a)$ always lies in $[302{,}400,\; 4{,}838{,}400]$, so it is positive and its conversion to a natural number (written $\kappa(a)$ below as well) is lossless.

**The next encoded target, $N(c, \ell, f)$ (the function called `calculateNextWork`).** For a compact word $c$ and integers $\ell$ ("last time") and $f$ ("first time"), put $\tau = \kappa(\ell - f)$ and

$$
u = \left\lfloor \frac{\left( D(c) \cdot \tau \right) \bmod 2^{256}}{T} \right\rfloor, \qquad
u' = \begin{cases} L & \text{if } L < u,\\ u & \text{otherwise,}\end{cases}
$$

i.e. $u' = \min(u, L)$. Then $N(c, \ell, f) = E(u')$, a compact word. The product $D(c)\cdot\tau$ is reduced modulo $2^{256}$ *before* the floor division by $T$; the cap at $L$ is applied *before* re-encoding, and nothing caps or checks the decoded value of the encoded result afterwards.

**Iterated retargeting, $A(c, P)$ (the function called `targetAfter`, defined in this bundle).** For a compact word $c$ and a finite list $P$ of pairs of integers, defined by recursion on the list:

$$
A(c, [\,]) = c, \qquad A\big(c, (\ell, f) :: P'\big) = A\big(N(c, \ell, f),\, P'\big).
$$

So for $P = [(\ell_1, f_1), (\ell_2, f_2), \dots, (\ell_k, f_k)]$, $A(c, P) = N(\cdots N(N(c, \ell_1, f_1), \ell_2, f_2) \cdots, \ell_k, f_k)$: the first pair of the list is applied first. The pairs are arbitrary integers; nothing relates $f_{i+1}$ to $\ell_i$, requires $f_i \le \ell_i$, or restricts their magnitude.


## Edge cases and what the quantifiers include

- $P = [\,]$: $k = 0$, $4^0 = 1$, $A(c, [\,]) = c$, and the conclusion reads $D(c) \le D(c)$.
- If $D(c) = 0$ the right-hand side is $0$ for every $P$, so the statement asserts that $D(A(c, P)) = 0$ for every list $P$ in that case; such $c$ are admitted by the hypothesis.
- The right-hand side $4^k \cdot D(c)$ grows without bound in $k$ and is not capped at $L$ or reduced modulo $2^{256}$; for $k$ large it exceeds $2^{256}$, above every possible value of $D$.
- Each step of $A$ decodes, multiplies by a clamped timespan in $[302{,}400, 4{,}838{,}400]$ modulo $2^{256}$, floor-divides by $T$, caps at $L$, and re-encodes (which can only lower the value, per the remark on $D \circ E$); the statement is about the final decoded value only.
- Pairs may have $\ell_i \le f_i$ or $\ell_i - f_i > 4{,}838{,}400$; there is no condition linking the pairs, no height condition, and no sign/overflow condition on $c$ or on intermediate words.
