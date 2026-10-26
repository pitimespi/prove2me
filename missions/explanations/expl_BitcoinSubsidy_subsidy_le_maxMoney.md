We prove $\mathrm{coreSubsidy}(h) \le \mathrm{MAX\_MONEY} = 2.1 \times 10^{15}$ for every height $h$.

By `BitcoinSubsidy.core_eq_spec` the subsidy equals $\lfloor 5 \times 10^{9} / 2^{k} \rfloor$ with $k = \lfloor h / 210000 \rfloor$. A quotient is at most its dividend, so the subsidy is at most $5 \times 10^{9}$, which is below $2.1 \times 10^{15}$. The subsidy is thus always within `MoneyRange`.
