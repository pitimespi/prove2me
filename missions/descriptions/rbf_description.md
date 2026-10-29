## The claim

Replace-by-fee (BIP125) is defended with two informal properties: "no free relay" (a transaction cannot be replaced over and over without each replacement paying for the bandwidth of the previous one) and the "pinning" observation (a counterparty who attaches high-fee descendants to a transaction can make it arbitrarily expensive to replace). Both are consequences of a single check in Bitcoin Core, `PaysForRBF`: a replacement must pay at least the fees of everything it evicts, plus the incremental relay fee for its own size. This mission transcribes that check and proves both properties as theorems about chains of replacements over an abstract mempool.

## What is proved

- **The rule** (`paysForRBF_iff`, `fee_strictly_increases`): `PaysForRBF` is one inequality, and under a positive incremental fee every evicted transaction paid strictly less than its replacement.
- **No free relay** (`bandwidth_paid`, the goal; `bandwidth_paid_total`, `bandwidth_paid_rate`, `bandwidth_paid_real`): along any chain of valid replacements the final fee covers the original fee plus the incremental relay fee of every relayed replacement, in Core's rounded-up `GetFee` and, because the rounding is upward, in exact rational arithmetic too.
- **Counting replacements** (`replacement_count_bound`, `replacement_count_bound_min_vsize`, `replacement_count_le_fee`, `replacement_count_bound_rate`): $n$ replacements cost at least $n$ incremental fees, so $n \le (\text{fee gained}) / \text{rate}$.
- **Pinning** (`pinning_cost`, `pinning_cost_tight`): descendants of total fee $F$ attached to a transaction raise the cost of replacing it by exactly $F$, no more and no less.
- **Rule 3** (`feeRateQ_lt_iff`, `evicted_feerate_dominated`, `min_direct_feerate_lt`): Core's cross-multiplied fee-rate comparison is the comparison of exact fractions, and every direct conflict's fee rate is strictly below the replacement's.

## What this rests on and what it does not say

`PaysForRBF` is transcribed from revision `a773e1e`, with `GetFee` as the exact ceiling `FeePerVSize::EvaluateFeeUp` and the default incremental relay fee of 100 sat/kvB of that revision. BIP125 rule 3 (`PaysMoreThanConflicts`) no longer exists at that revision, where the cluster mempool replaced it with a feerate-diagram check; the three rule-3 theorems use its last form (v29.0) and the others do not depend on it. The mempool is abstract: eviction sets are given, not computed; fees are modified fees; package relay, TRUC, sibling eviction, opt-in signalling and the structural rules are not modelled, and each only shrinks the set of valid replacements. ([`rbf.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp))
