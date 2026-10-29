# Read-back: `BitcoinToLocal.serialize_length`

**Statement.** For every integer $n$ and every natural number $k$ such that

$$
|n| < 256^{k}
$$

(where $|n|$ is the absolute value of $n$ taken as a natural number), the byte string $\mathrm{serialize}(n)$ has length at most $k + 1$:

$$
\big|\mathrm{serialize}(n)\big| \le k + 1 .
$$

**The function `serialize`.** It is the script-number encoding $\mathbb{Z} \to$ byte strings defined as follows.

- $\mathrm{serialize}(0) = [\,]$, the empty byte string.
- For $n \ne 0$: let $m$ be the list of base-$256$ digits of $|n|$ in little-endian order with no trailing zero bytes (the digit list is produced by repeatedly taking the remainder and quotient by $256$ until the value is $0$, so $m$ is non-empty with non-zero last byte). Let $\mathrm{neg}$ be the truth of $n < 0$.
  - If the last byte of $m$ has its $\mathtt{0x80}$ bit set, the result is $m$ followed by one extra byte: $\mathtt{0x80}$ if $\mathrm{neg}$, and $\mathtt{0x00}$ otherwise.
  - Otherwise, if $\mathrm{neg}$, the result is $m$ with the $\mathtt{0x80}$ bit set on its last byte.
  - Otherwise the result is $m$ itself.

**Edge cases.** For $k = 0$ the hypothesis reads $|n| < 1$, which forces $n = 0$, and the conclusion is $0 \le 1$. For $k \ge 1$ the hypothesis admits negative $n$ with $|n| \le 256^{k} - 1$, and the conclusion allows the encoding to be one byte longer than $k$ (accounting for a possible extra sign byte). The theorem bounds the length only from above; it says nothing about a lower bound or about the content of the bytes.
