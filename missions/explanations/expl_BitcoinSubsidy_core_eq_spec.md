We prove that the transcription of `GetBlockSubsidy` agrees with the halving schedule at every height $h$:
$$\mathrm{coreSubsidy}(h) = \left\lfloor \frac{5 \times 10^{9}}{2^{\lfloor h/210000 \rfloor}} \right\rfloor .$$

**Idea.** Write $k = \lfloor h / 210000 \rfloor$. The implementation returns $0$ when $k \ge 64$ and $(5 \times 10^{9}) \gg k$ otherwise; the schedule always divides. A right shift of a natural number by $k$ bits is division by $2^k$, so the two sides coincide when $k < 64$. When $k \ge 64$, the divisor $2^k \ge 2^{64}$ exceeds $5 \times 10^{9}$, so the schedule's quotient is $0$ as well.

**Step 1 ($k \ge 64$).** $5 \times 10^{9} < 2^{64} \le 2^{k}$, hence $\lfloor 5 \times 10^{9} / 2^{k} \rfloor = 0$, matching the guarded branch.

**Step 2 ($k < 64$).** $(5 \times 10^{9}) \gg k = \lfloor 5 \times 10^{9} / 2^{k} \rfloor$ by the definition of the shift on natural numbers.

The source's guard against an undefined C++ shift is therefore never the operative reason for a zero subsidy; division already gives zero there.
