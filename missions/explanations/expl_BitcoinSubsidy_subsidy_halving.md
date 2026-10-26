We prove the halving recurrence $\mathrm{coreSubsidy}(h + 210000) = \lfloor \mathrm{coreSubsidy}(h) / 2 \rfloor$ for every height $h$.

By `BitcoinSubsidy.core_eq_spec` both sides are expressed through the schedule. Adding one full interval increases the halving count by exactly one: $\lfloor (h + 210000) / 210000 \rfloor = \lfloor h / 210000 \rfloor + 1$. Writing $k$ for $\lfloor h/210000 \rfloor$, the left side is $\lfloor 5 \times 10^{9} / 2^{k+1} \rfloor$, and since $2^{k+1} = 2^{k} \cdot 2$, nested floor division gives
$$\left\lfloor \frac{5 \times 10^{9}}{2^{k} \cdot 2} \right\rfloor = \left\lfloor \frac{\lfloor 5 \times 10^{9} / 2^{k} \rfloor}{2} \right\rfloor ,$$
which is the right side.
