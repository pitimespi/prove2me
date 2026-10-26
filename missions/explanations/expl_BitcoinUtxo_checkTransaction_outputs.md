We prove that a transaction accepted by `checkTransaction` has pairwise distinct inputs and every output value in $[0, \mathrm{MAX\_MONEY}]$.

`checkTransaction` is a conjunction of four Boolean tests; the last is the decidable `Nodup` of the input list, which gives distinctness directly. The third is that the output loop returns some total; by induction on the output list, a successful loop means every element passed the two value tests, $\neg(v < 0)$ and $\neg(\mathrm{MAX\_MONEY} < v)$, which is the stated range. The running-total test is not needed for this conclusion.
