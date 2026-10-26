We prove $\mathrm{issuedBelow}(n) < \mathrm{MAX\_MONEY} = 2.1 \times 10^{15}$ for every $n$.

By `BitcoinSubsidy.issuance_le_total`, $\mathrm{issuedBelow}(n) \le 2{,}099{,}999{,}997{,}690{,}000$, and this constant is strictly below $2{,}100{,}000{,}000{,}000{,}000$; the gap is $2{,}310{,}000$ satoshi, the accumulated remainders of the thirty-three halvings. Hence no chain length lets the subsidy schedule issue `MAX_MONEY` or more in total.
