We prove that the overflow flag of `SetCompact` is exactly the condition that the encoded value does not fit in 256 bits:
$$\mathrm{compactOverflow}(c) = \mathtt{true} \iff 2^{256} \le \mathrm{specTarget}(c),$$
for every 32-bit word $c$ with size byte $S < 256$ and 23-bit mantissa $W < 2^{23}$.

**Idea.** For $S > 3$ the exact value is $W \cdot 256^{S-3} = W \cdot 2^{8(S-3)}$. It reaches $2^{256}$ exactly when $W \ge 2^{256 - 8(S-3)} = 2^{280 - 8S}$. The three thresholds in the source are this condition evaluated at the only sizes where it can hold with a 23-bit mantissa: $S = 33$ needs $W \ge 2^{16}$, $S = 34$ needs $W \ge 2^{8}$, and $S \ge 35$ needs only $W \ge 1$; for $S \le 32$ the value is below $2^{23} \cdot 2^{232} = 2^{255}$.

**Step 1 ($S \le 3$).** The value is a quotient of $W$, hence below $2^{23} < 2^{256}$, and the flag is clear because every clause needs $S > 32$.

**Step 2 ($4 \le S \le 32$).** $W \cdot 256^{S-3} \le 2^{23} \cdot 256^{29} = 2^{255} < 2^{256}$; no clause applies.

**Step 3 ($S = 33$).** $2^{256} = 2^{16} \cdot 2^{240}$, so $2^{256} \le W \cdot 2^{240}$ iff $W \ge 2^{16}$ iff $W > \mathtt{0xffff}$, the third clause (and $W \ne 0$ follows).

**Step 4 ($S = 34$).** Likewise with $2^{256} = 2^{8} \cdot 2^{248}$ and the second clause $W > \mathtt{0xff}$.

**Step 5 ($S \ge 35$).** $256^{S-3} \ge 256^{32} = 2^{256}$, so the value reaches $2^{256}$ iff $W \ge 1$, the first clause.

The flag is therefore not an approximation of fitting in 256 bits; it is that condition exactly.
