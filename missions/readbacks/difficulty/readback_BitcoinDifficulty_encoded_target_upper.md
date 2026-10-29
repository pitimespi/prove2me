# Read-back: theorem `BitcoinDifficulty.encoded_target_upper`

## Statement

**Binders (universally quantified).**

- $c$, a compact word (a 32-bit word, named `bits`);
- $\ell$ and $f$, integers (named `lastTime`, `firstTime`), unrelated to each other.

**Hypothesis.**

- (hb) $D(c) \le L = 2^{224} - 1$.

**Conclusion.**

$$
D\big( N(c, \ell, f) \big) \;\le\; 4 \cdot D(c),
$$

where $4 \cdot D(c)$ is an ordinary natural-number product (no reduction modulo anything, no cap at $L$ on the right-hand side). Unfolding $N$: with $\tau = \kappa(\ell - f)$, $u = \big\lfloor \big((D(c)\cdot\tau) \bmod 2^{256}\big)/T \big\rfloor$ and $u' = \min(u, L)$, the left-hand side is $D(E(u'))$ — the decoded value of the re-encoded, capped next target. The inequality is non-strict.

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


## Edge cases and what the quantifiers include

- $\ell$ and $f$ range over all integers; $\ell - f$ may be zero or negative (clamped to $302{,}400$) or arbitrarily large (clamped to $4{,}838{,}400 = 4T$).
- If $D(c) = 0$ the right-hand side is $0$, so the statement asserts $D(N(c, \ell, f)) = 0$ for every $\ell, f$ in that case; the hypothesis admits all such words (zero mantissa, top byte $0$, top byte $\ge 35$, etc.).
- The hypothesis constrains only the decoded value; the sign bit (bit 23) and the overflow conditions of the original code are not mentioned.
- The cap at $L$ inside $N$ applies before encoding; the bound $4 \cdot D(c)$ on the right may exceed $L$ (it does whenever $D(c) > L/4$), and the statement does not assert $D(N(c,\ell,f)) \le L$.
- When $D(c) \le L$, $D(c) \cdot \tau < 2^{247} < 2^{256}$, so the modular reduction inside $N$ is inactive for every admitted $c$; it is still part of the literal statement.
