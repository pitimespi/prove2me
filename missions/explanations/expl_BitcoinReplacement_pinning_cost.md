`totalFee` is monotone under the multiset order (`Multiset.le_iff_exists_add`), so `t.fee + totalFee D ≤ totalFee evicted`, and `paysForRBF_iff` adds the incremental fee.
