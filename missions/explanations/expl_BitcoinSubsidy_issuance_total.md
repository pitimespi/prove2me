We prove $\mathrm{issuedBelow}(6{,}930{,}000) = 2{,}099{,}999{,}997{,}690{,}000$.

**Idea.** The subsidy is constant on each interval of $210{,}000$ heights, so the running sum over whole intervals is $210{,}000$ times the sum of one subsidy per interval. Thirty-three intervals reach the zero height, and the thirty-three-term interval sum is a finite computation.

**Step 1 (constancy within an interval).** For $m$ and $j < 210000$, $\lfloor (210000\,m + j) / 210000 \rfloor = m$, so by `BitcoinSubsidy.core_eq_spec`, $\mathrm{coreSubsidy}(210000\,m + j) = \lfloor 5 \times 10^{9} / 2^{m} \rfloor$.

**Step 2 (partial interval).** By induction on $j \le 210000$,
$$\mathrm{issuedBelow}(210000\,m + j) = \mathrm{issuedBelow}(210000\,m) + j \cdot \lfloor 5 \times 10^{9} / 2^{m} \rfloor .$$

**Step 3 (whole intervals).** By induction on $m$, using Step 2 with $j = 210000$,
$$\mathrm{issuedBelow}(210000\,m) = 210000 \cdot \mathrm{intervalSum}(m), \qquad \mathrm{intervalSum}(m) = \sum_{i<m} \lfloor 5 \times 10^{9} / 2^{i} \rfloor .$$

**Step 4.** At $m = 33$ the interval sum evaluates to $9{,}999{,}999{,}989$, and $210000 \cdot 9{,}999{,}999{,}989 = 2{,}099{,}999{,}997{,}690{,}000$.
