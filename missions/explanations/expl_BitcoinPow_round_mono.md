We prove that the rounding map $r(v) = \mathrm{setCompact}(\mathrm{getCompact}(v))$ is monotone: $v \le w < 2^{256} \implies r(v) \le r(w)$.

**Idea.** By the closed form established for `BitcoinPow.getCompact_le`, $r(v) = \lfloor v/2^{e} \rfloor \cdot 2^{e}$ with $e$ depending only on the top-bit index $L(v)$, and $e \le L(v)$. Two values with the same top bit are rounded on the same grid; a value with a lower top bit lies entirely below the retained top bit of the other.

**Step 1 ($v = 0$).** $r(0) = 0 \le r(w)$.

**Step 2 ($L(v) = L(w)$).** Same $e$, and $\lfloor v/2^{e} \rfloor \le \lfloor w/2^{e} \rfloor$, so $r(v) \le r(w)$.

**Step 3 ($L(v) < L(w)$).** $r(v) \le v < 2^{L(v)+1} \le 2^{L(w)} \le r(w)$. The last inequality is the top-bit retention: since $e \le L(w)$, $2^{L(w)} = 2^{L(w)-e} \cdot 2^{e}$ and $\lfloor w/2^{e} \rfloor \ge 2^{L(w)-e}$, whence $r(w) \ge 2^{L(w)}$.

This is the property `PermittedDifficultyTransition` relies on when it compares a decoded word against re-encoded bounds.
