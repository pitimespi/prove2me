We prove $\mathrm{coreSubsidy}(h) = 0 \iff h \ge 6{,}930{,}000$ for every height $h$.

**Idea.** By `BitcoinSubsidy.core_eq_spec` the subsidy is $\lfloor 5 \times 10^{9} / 2^{k} \rfloor$ with $k = \lfloor h/210000 \rfloor$, and a quotient of natural numbers is zero exactly when the dividend is below the divisor. So the subsidy vanishes exactly when $5 \times 10^{9} < 2^{k}$. The two relevant powers are $2^{32} = 4{,}294{,}967{,}296 \le 5 \times 10^{9} < 8{,}589{,}934{,}592 = 2^{33}$, so this holds exactly when $k \ge 33$.

**Step 1 (zero implies $k \ge 33$).** If $k \le 32$ then $2^{k} \le 2^{32} \le 5 \times 10^{9}$, contradicting $5 \times 10^{9} < 2^{k}$.

**Step 2 ($k \ge 33$ implies zero).** Then $2^{k} \ge 2^{33} > 5 \times 10^{9}$.

**Step 3.** $k \ge 33$ is equivalent to $h \ge 33 \cdot 210000 = 6{,}930{,}000$ by the characterization of floor division: $33 \le \lfloor h / 210000 \rfloor \iff 33 \cdot 210000 \le h$.
