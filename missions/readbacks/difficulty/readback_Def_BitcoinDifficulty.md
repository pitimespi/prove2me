# Read-back: `Def_BitcoinDifficulty.lean`

This file introduces two definitions, `rawNextTarget` and `targetAfter`, in terms of the imported proof-of-work definitions. The imported notions they use are expanded first; then one paragraph per declaration, in file order.

## Imported notions used

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


## Declaration 1: `rawNextTarget`

**Binders.** A natural number $t$ (named `lastTarget`; any natural number, with no upper bound — in particular not required to be below $2^{256}$ or $L$), and two integers $\ell$ (`lastTime`) and $f$ (`firstTime`), each positive, zero or negative, with no ordering between them.

**Value.** A natural number, defined as follows. Let $\tau = \kappa(\ell - f)$, the clamped difference, a natural number in $[302{,}400, 4{,}838{,}400]$. Let

$$
q = \left\lfloor \frac{(t \cdot \tau) \bmod 2^{256}}{T} \right\rfloor ,
$$

where the product $t \cdot \tau$ is first reduced modulo $2^{256}$ and the result is then divided by $T = 1{,}209{,}600$ with the remainder discarded (the source writes the two operations left to right, so the reduction precedes the division). Then

$$
R(t, \ell, f) = \begin{cases} L & \text{if } L < q,\\ q & \text{otherwise,} \end{cases}
$$

that is, $R(t,\ell,f) = \min(q, L)$ with $L = 2^{224} - 1$.

**Edge cases built into the definition.** If $\ell - f \le 302{,}400$ (including every case with $\ell \le f$, i.e. zero or negative differences), $\tau = 302{,}400$; if $\ell - f \ge 4{,}838{,}400$, $\tau = 4{,}838{,}400$. If $t = 0$ then $R = 0$. If $t \cdot \tau \ge 2^{256}$ (possible for $t \ge 2^{256}/4{,}838{,}400$, which is above $L$), the reduction modulo $2^{256}$ discards the high part before dividing. The result is always $\le L$, and no encoding step is applied: $R$ is the value that `calculateNextWork` would pass to $E$, so that $N(c, \ell, f) = E(R(D(c), \ell, f))$ for every compact word $c$.

## Declaration 2: `targetAfter`

**Binders.** A compact word $c$ (a 32-bit word, named `bits`) and a finite list $P$ of pairs of integers $(\ell_i, f_i)$, where by the definition's naming the first component of each pair is the "last time" and the second the "first time" of that period.

**Value.** A compact word, defined by recursion on the list:

$$
A(c, [\,]) = c, \qquad A\big(c, (\ell, f) :: P'\big) = A\big(N(c, \ell, f), P'\big).
$$

Hence for $P = [(\ell_1, f_1), \dots, (\ell_k, f_k)]$,

$$
A(c, P) = N\big(\cdots N(N(c, \ell_1, f_1), \ell_2, f_2) \cdots, \ell_k, f_k\big),
$$

where each application of $N$ decodes the current word with $D$, multiplies by the clamped timespan $\kappa(\ell_i - f_i)$ modulo $2^{256}$, floor-divides by $T$, caps at $L$, and re-encodes with $E$ (so each step rounds the value to a compact word before the next step decodes it).

**Edge cases built into the definition.** For the empty list, $A(c, [\,]) = c$ unchanged, whatever $c$ is (no decoding or validity check). The pairs are independent integers: nothing requires $f_i \le \ell_i$, nothing relates $f_{i+1}$ to $\ell_i$, and no height or interval condition is consulted (unlike `nextWorkRequired`, every list element triggers a retarget). The initial word $c$ is unconstrained: it may have its bit 23 set, decode to $0$, or have a top byte $\ge 35$.
