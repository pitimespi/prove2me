We prove $\mathrm{issuedBelow}(n) \le 2{,}099{,}999{,}997{,}690{,}000$ for every $n$.

**Idea.** The running sum is monotone in $n$, and it stops growing at the zero height because every later subsidy is zero. So every value of the sum is at most its value at the zero height, which `BitcoinSubsidy.issuance_total` evaluates.

**Step 1 (monotone).** $\mathrm{issuedBelow}(a) \le \mathrm{issuedBelow}(b)$ for $a \le b$, by induction on $b$: each step adds a natural number.

**Step 2 (stable).** For $n \ge 6{,}930{,}000$, $\mathrm{issuedBelow}(n) = \mathrm{issuedBelow}(6{,}930{,}000)$, by induction on $n$: each added term $\mathrm{coreSubsidy}(n)$ is zero by `BitcoinSubsidy.subsidy_zero_iff`.

**Step 3.** If $n \ge 6{,}930{,}000$ the sum equals the total by Step 2; otherwise it is at most the total by Step 1. In both cases the bound follows from `issuance_total`.
