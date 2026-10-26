We prove that along a chain in which every block satisfies `time-too-old` against its predecessor, the median time past of any suffix is at most that of any shorter suffix: for $i \le j \le n$, $\mathrm{MTP}(\mathrm{drop}_j) \le \mathrm{MTP}(\mathrm{drop}_i)$.

**Idea.** Going from the suffix starting at $j + 1$ to the one starting at $j$ prepends the block time $t_j$, which by hypothesis exceeds the median of the suffix starting at $j + 1$; `BitcoinHeader.mtp_mono` says the median then does not decrease. The statement for arbitrary $i \le j$ follows by chaining these one-step inequalities.

**Argument.** Induction on $j$. For $j = 0$, $i = 0$ and the two suffixes coincide. For $j + 1$ with $i \le j + 1$: if $i = j + 1$ the suffixes coincide; otherwise $j < n$, the suffix at $j$ is $t_j$ prepended to the suffix at $j + 1$, the hypothesis at position $j$ supplies $\mathrm{MTP}(\mathrm{drop}_{j+1}) < t_j$, so `mtp_mono` gives $\mathrm{MTP}(\mathrm{drop}_{j+1}) \le \mathrm{MTP}(\mathrm{drop}_j)$, and the induction hypothesis gives $\mathrm{MTP}(\mathrm{drop}_j) \le \mathrm{MTP}(\mathrm{drop}_i)$.

This is the clock monotonicity that time-based lock-times rely on: the chain's times need not themselves be increasing; the median rule alone forces the median to be.
