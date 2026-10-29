# Read-back: theorem `BitcoinDifficulty.requiredBits_le`

## Statement

**Binders (universally quantified).**

- $S$, a chain state: a record consisting of a finite list of headers $[H_0, \dots, H_{n-1}]$ ($n \ge 0$, possibly empty) and a ledger. No validity, chaining, ordering or length property of $S$ is assumed.

Write $c_{\mathrm{tip}} = \mathrm{tip}(S).\mathrm{bits} \bmod 2^{32}$ for the compact word formed from the bits field of the tip header (the last header of the list, or the genesis header $G_0$ if the list is empty).

**Hypothesis.**

- (hb) $D(c_{\mathrm{tip}}) \le L = 2^{224} - 1$.

**Conclusion.**

$$
D\big( \mathrm{requiredBits}(S) \big) \;\le\; 4 \cdot D(c_{\mathrm{tip}}),
$$

with $4 \cdot D(c_{\mathrm{tip}})$ the plain natural-number product and a non-strict inequality. Unfolding $\mathrm{requiredBits}(S)$: let $h = \mathrm{tipHeight}(S) = n - 1$ (truncated, so $0$ if $n = 0$), let $j = h - 2015$ (truncated, so $0$ if $h \le 2015$), let $F = H_j$ if $j < n$ and $F = G_0$ otherwise. Then

- if $(h + 1) \bmod 2016 \ne 0$: $\mathrm{requiredBits}(S) = c_{\mathrm{tip}}$, and the conclusion reads $D(c_{\mathrm{tip}}) \le 4 \cdot D(c_{\mathrm{tip}})$;
- if $(h + 1) \bmod 2016 = 0$: $\mathrm{requiredBits}(S) = N\big(c_{\mathrm{tip}},\; \mathrm{tip}(S).\mathrm{time},\; F.\mathrm{time}\big)$ (times read as integers), and the conclusion reads $D\big(N(c_{\mathrm{tip}}, \mathrm{tip}(S).\mathrm{time}, F.\mathrm{time})\big) \le 4 \cdot D(c_{\mathrm{tip}})$.

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

**Chain states and the required bits (from the imported block-validation definitions).**

- A *header* is a record with fields: version (an integer), previous-block hash and Merkle root (byte strings), time (a natural number), bits (a natural number, *unbounded* — not restricted to 32 bits), nonce (a natural number). The *genesis header* $G_0$ is the fixed header with version $1$, zero previous hash, time $1{,}231{,}006{,}505$, bits $\mathtt{0x1d00ffff} = 486{,}604{,}799$, nonce $2{,}083{,}236{,}893$.
- A *chain state* $S$ is a record with two fields: a finite list of headers $S.\mathrm{headers} = [H_0, H_1, \dots, H_{n-1}]$ (possibly empty, $n \ge 0$) and a ledger $S.\mathrm{utxo}$ (not used by the statement below). No property of $S$ (chaining of headers, validity, length, time ordering, reachability from genesis) is assumed.
- $\mathrm{tipHeight}(S) = n - 1$ with truncated natural-number subtraction, so $\mathrm{tipHeight}(S) = 0$ when $n = 0$ as well as when $n = 1$.
- $\mathrm{tip}(S) = H_{n-1}$, the last header of the list, or $G_0$ if the list is empty.
- $I = \lfloor T / 600 \rfloor = 2016$ (the value called `difficultyAdjustmentInterval`).
- $\mathrm{nextWorkRequired}(h, c, \ell, f)$ for a natural number $h$, a compact word $c$ and integers $\ell, f$ is $c$ itself if $(h + 1) \bmod 2016 \neq 0$, and $N(c, \ell, f)$ if $(h+1) \bmod 2016 = 0$.
- $\mathrm{requiredBits}(S)$: let $j = \mathrm{tipHeight}(S) - 2015$ with truncated subtraction (so $j = 0$ whenever $\mathrm{tipHeight}(S) \le 2015$), and let $F = H_j$ if $j < n$, else $F = G_0$ (this default case arises only when the header list is empty). Then
$$
\mathrm{requiredBits}(S) = \mathrm{nextWorkRequired}\big(\mathrm{tipHeight}(S),\; \mathrm{tip}(S).\mathrm{bits} \bmod 2^{32},\; \mathrm{tip}(S).\mathrm{time},\; F.\mathrm{time}\big),
$$
where the two times (natural numbers) are read as integers and the tip's bits field is reduced modulo $2^{32}$ to form a compact word.


## Edge cases and what the quantifiers include

- The header list may be empty: then $\mathrm{tip}(S) = G_0$, $h = 0$, $F = G_0$, $(0+1) \bmod 2016 \ne 0$, so $\mathrm{requiredBits}(S) = c_{\mathrm{tip}} = \mathtt{0x1d00ffff}$ and the conclusion is $D(c_{\mathrm{tip}}) \le 4 D(c_{\mathrm{tip}})$.
- The retarget branch is taken exactly when $n \bmod 2016 = 0$ with $n \ge 1$, i.e. $n = 2016, 4032, \dots$; for such $n$, $j = n - 2016 \ge 0$ and $F = H_{n-2016}$ is the header $2015$ positions before the tip. In every other case the required bits are the tip's own bits word.
- The header's bits field is an unbounded natural number; only its residue modulo $2^{32}$ enters, both in the hypothesis and in the conclusion.
- The header times are natural numbers with no ordering assumed: $F.\mathrm{time}$ may exceed $\mathrm{tip}(S).\mathrm{time}$, in which case the difference is negative and clamped to $302{,}400$; a difference above $4{,}838{,}400$ is clamped to that value.
- No assumption is made that the headers form a chain, that the tip is reachable from genesis, that the list has length $\ge 2016$, or that any header's bits decode to a non-zero or non-overflowing target; only $D(c_{\mathrm{tip}}) \le L$ is assumed. If $D(c_{\mathrm{tip}}) = 0$ the right-hand side is $0$.
- The ledger component of $S$ plays no role in the statement.
