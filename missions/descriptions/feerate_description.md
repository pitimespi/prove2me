## The claim

At the pinned revision, Bitcoin Core's cluster mempool replaced BIP125 rule 3 ("the replacement's feerate must exceed every conflict's") with a single check: the replacement must strictly improve the *feerate diagram* of the affected clusters. The replace-by-fee mission had to take rule 3 from v29.0 for that reason. This mission transcribes the actual check (`FeeFrac`, `CompareChunks`, `ImprovesFeerateDiagram`), proves that Core's sweep computes the mathematical comparison of the two diagrams, and connects it to the existing no-free-relay theorems.

## What is proved

- **The arithmetic** (`byRatio_eq_compare_ratio`, `byRatio_lt_iff`, `div_round_down_eq_floor`, `div_round_up_eq_ceil`, `mulFallback_value`, `divFallback_eq_div`, `evaluateFeeDown_eq_floor`, `evaluateFeeUp_eq_ceil`, `getFee_eq_evaluateFeeUp`): Core's cross-multiplied comparison is the comparison of exact ratios; its divisions round as named on both code paths; the replacement mission's `GetFee` is `EvaluateFeeUp`.
- **The diagram** (`diagram_at_zero`, `diagram_total`, `diagram_concave`): starts at the origin, ends at the total fee, and is concave for chunkings with non-increasing feerates.
- **The check** (`compare_chunks_sound`, `improvesFeerateDiagram_iff`): `CompareChunks` returns `greater`, `less`, `equivalent` or `unordered` exactly according to the pointwise comparison of the two piecewise-linear functions; `ImprovesFeerateDiagram` is "strictly better".
- **What it guarantees** (`improves_total_fee`, `improves_total_fee_not_strict`, `no_free_relay_diagram`, the goal): a strict improvement never lowers the total fee but need not raise it, and together with `PaysForRBF` the replacement adds at least the incremental relay fee: no free relay holds under the pinned revision's actual rules.

## Vectors

All eleven `CompareChunks` cases of Core's `rbf_tests.cpp`, the `FeeFrac` arithmetic cases of `feefrac_tests.cpp` (including the fast-path thresholds and issue #32294), and hand-computed diagrams agree (`tests/FeerateDiagramVectors.lean`).

## What this rests on and what it does not say

The chunk lists are input: the linearization of the affected clusters (`txmempool.cpp`, `txgraph.cpp`) is not modelled, nor which transactions belong to the clusters; `no_free_relay_diagram` relates the diagrams to a `Replacement` by a hypothesis on total fees. Fees and sizes are unbounded integers. ([`feefrac.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp), [`rbf.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp))
