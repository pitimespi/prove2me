We prove that `GetCompact` never produces a negative or overflowing word, for every $v < 2^{256}$.

**Idea.** The word is assembled as $m \lor (S' \cdot 2^{24})$ from a pre-adjustment mantissa $M < 2^{24}$ and a size $S \le 32$. After the bit-23 adjustment the mantissa $m$ is below $2^{23}$ and the size $S' \le 33$; a sign bit never appears, and the overflow thresholds cannot be met.

**Step 1 ($M < 2^{24}$).** With $L$ the top-bit index of $v$ and $S = \lfloor L/8 \rfloor + 1 \le 32$: for $S \le 3$, $M = v \cdot 2^{8(3-S)} < 2^{L+1+8(3-S)} \le 2^{24}$; for $S > 3$, $M = \lfloor v/2^{8(S-3)} \rfloor < 2^{L+1-8(S-3)} \le 2^{24}$. The case $v = 0$ is evaluated directly.

**Step 2 (adjusted).** If bit 23 of $M$ is set, $m = \lfloor M/256 \rfloor < 2^{16}$ and $S' = S + 1 \le 33$. The size clauses $S' > 34$ and $S' > 33$ fail; the clause $m > \mathtt{0xffff}$ fails since $m < 2^{16}$.

**Step 3 (not adjusted).** Then $m = M < 2^{23}$ (bit 23 clear) and $S' = S \le 32$, so every clause fails on the size alone.

In both cases the assembled word's mantissa is below $2^{23}$, so reading back its fields gives sign bit clear.
