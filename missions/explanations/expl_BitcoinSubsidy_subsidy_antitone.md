We prove that the subsidy is non-increasing: $h_1 \le h_2 \implies \mathrm{coreSubsidy}(h_2) \le \mathrm{coreSubsidy}(h_1)$.

**Idea.** By `BitcoinSubsidy.core_eq_spec` both sides are quotients of the same dividend $5 \times 10^{9}$ by powers of two, and dividing by a larger power gives a smaller quotient.

**Argument.** From $h_1 \le h_2$ we get $\lfloor h_1/210000 \rfloor \le \lfloor h_2/210000 \rfloor$, hence $2^{\lfloor h_1/210000 \rfloor} \le 2^{\lfloor h_2/210000 \rfloor}$, and so
$$\left\lfloor \frac{5 \times 10^{9}}{2^{\lfloor h_2/210000 \rfloor}} \right\rfloor \le \left\lfloor \frac{5 \times 10^{9}}{2^{\lfloor h_1/210000 \rfloor}} \right\rfloor ,$$
since the dividend is fixed and the divisors are positive.
