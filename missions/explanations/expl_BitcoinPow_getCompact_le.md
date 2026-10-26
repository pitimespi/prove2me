We prove that re-encoding rounds down: $\mathrm{setCompact}(\mathrm{getCompact}(v)) \le v$ for every $v < 2^{256}$.

**Idea.** For $v \ne 0$ let $L = \lfloor \log_2 v \rfloor$ be the index of its top bit. We establish the closed form
$$\mathrm{setCompact}(\mathrm{getCompact}(v)) = \left\lfloor \frac{v}{2^{e}} \right\rfloor \cdot 2^{e}, \qquad e = e(L),$$
where $e(L) = 0$ for $L < 16$ and otherwise $e(L) = 8\lfloor L/8 \rfloor - 16$, plus $8$ when $L \equiv 7 \pmod 8$. The right-hand side is $v$ with its low $e$ bits cleared, which is at most $v$. For $v = 0$ both sides are $0$ by direct evaluation.

**Step 1 (the mantissa before adjustment).** With $S = \lfloor L/8 \rfloor + 1$, the pre-adjustment mantissa $M$ is $v \cdot 2^{8(2 - \lfloor L/8 \rfloor)}$ when $S \le 3$ and $\lfloor v / 2^{8\lfloor L/8 \rfloor - 16} \rfloor$ otherwise; in both cases $2^{(L \bmod 8) + 16} \le M < 2^{(L \bmod 8) + 17}$, so $M < 2^{24}$ and the two reductions modulo $2^{64}$ and $2^{32}$ are the identity.

**Step 2 (the adjustment).** Bit 23 of $M$ is set iff $M \ge 2^{23}$ iff $L \equiv 7 \pmod 8$. When it is, the mantissa becomes $\lfloor M / 256 \rfloor$ and the size increments.

**Step 3 (reading the fields).** The assembled word is $m \lor (S' \cdot 2^{24})$ with $m < 2^{23}$, so its size byte is $S'$, its mantissa $m$, and its sign bit clear.

**Step 4 (decoding).** Decoding re-shifts $m$ by $8(S' - 3)$, which in every case is $\lfloor v / 2^{e} \rfloor \cdot 2^{e}$ with $e$ as above; the register reduction modulo $2^{256}$ is the identity because the result is at most $v < 2^{256}$. Three cases arise: $S' \le 3$ (exact, $e = 0$), $L = 23$ with adjustment ($e = 8$), and $L \ge 24$ ($e = 8\lfloor L/8 \rfloor - 16$ or that plus $8$).
