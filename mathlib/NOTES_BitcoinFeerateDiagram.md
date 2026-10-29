# NOTES — `BitcoinFeerateDiagram`: Bitcoin Core's cluster-mempool RBF check `ImprovesFeerateDiagram`

Files: `Definitions/Def_BitcoinFeerateDiagram.lean` (model, imports `Def_BitcoinReplacement`),
`Solutions/Sol_BitcoinFeerateDiagram_all.lean` (proofs, 17 public theorems, no `sorry`, axioms of each
public theorem ⊆ {propext, Classical.choice, Quot.sound}), `tests/FeerateDiagramVectors.lean`
(kernel-checked vectors).

## Sources (read as data)

All at bitcoin/bitcoin revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, fetched from
`raw.githubusercontent.com/bitcoin/bitcoin/<rev>/src/...`:

| What | File | Lines |
|---|---|---|
| `struct FeeFrac { int64_t fee; int32_t size; }`, ctor `FeeFrac()` = (0,0) | `util/feefrac.h` | 20, 88–92 |
| `MulFallback` (64×32 → pair) | `util/feefrac.h` | 25–30 |
| `DivFallback` (96/32 division, rounding) | `util/feefrac.h` | 40–59 |
| `Mul` / `Div` (`__int128` versions) | `util/feefrac.h` | 64–67, 74–82 (fallback aliases 84–85) |
| `IsEmpty`, `operator+`, `operator-` | `util/feefrac.h` | 101, 120–131 |
| `EvaluateFee<RoundDown>`, `EvaluateFeeDown/Up` | `util/feefrac.h` | 147–175 |
| `CeilDiv` | `util/overflow.h` | 70–74 |
| comment "implied diagram … starts at (0, 0) … extends infinitely to the right with a horizontal line" | `util/feefrac.h` | 177–186 |
| `ByRatio::operator<=>` (cross-multiplication) | `util/feefrac.h` | 217–240 |
| `CompareChunks` (the sweep) | `util/feefrac.cpp` | 12–75 |
| `PaysForRBF` (rules #3/#4) | `policy/rbf.cpp` | 100–125 |
| `ImprovesFeerateDiagram` | `policy/rbf.cpp` | 127–140 |
| `ChangeSet::CalculateChunksForRBF` | `txmempool.cpp` | 1042–1051 |
| `TxGraphImpl::GetMainStagingDiagrams` (old = conflicting main clusters' chunks, new = staging clusters' chunks, both sorted by `ByRatioNegSize` descending) | `txgraph.cpp` | 2810–2834 |
| test vectors `feerate_chunks_utilities` | `test/rbf_tests.cpp` | 485–559 |
| test vectors `feefrac_operators` | `test/feefrac_tests.cpp` | 12–155 |

## Transcription (namespace `BitcoinFeerateDiagram`)

* `FeeFrac = {fee : ℤ, size : ℤ}` with `0`, `+`, `-` componentwise; `IsEmpty a := a.size = 0`.
* `FeeFrac.mul a b = a * b` (`Mul`); `mulFallback a b = ((a / 2^32) * b + low / 2^32, low % 2^32)`
  with `low = (a % 2^32) * b` (`static_cast<uint32_t>` = `% 2^32`, `>> 32` = floor division).
* `FeeFrac.div n d rd = n.tdiv d + ((tmod > 0) − (tmod ≠ 0 ∧ rd))` (C++ `/`, `%` truncate =
  `Int.tdiv`, `Int.tmod`); `divFallback` the 96/32 version line by line.
* `evaluateFee f atSize rd`: the `uint64_t` fast path if `0 ≤ fee < 2^33` (`/` resp. `ceilDiv`),
  else `div (mul fee atSize) size rd`; `evaluateFeeDown/Up` = `rd = true/false`.
* `byRatioCmp a b = compare (a.fee * b.size) (b.fee * a.size)`; `ratio a = fee / size : ℚ`.
* `PartialOrdering = less | equivalent | greater | unordered` (`std::partial_ordering`);
  `boolCompare b0 b1` = `better_somewhere[0] <=> better_somewhere[1]`.
* `sweep rem0 rem1 acc0 acc1 b0 b1`: one equation per iteration of the `do … while(true)` loop of
  `CompareChunks` (`util/feefrac.cpp` 29–71): the state is the unprocessed suffixes
  `chunk[i][next_index[i]..]`, `accum[i]`, `better_somewhere[i]`; the four arms are
  both done (→ `boolCompare`), only side 1 done (P = next point of 0 vs slope `FeeFrac(0,1)`), only
  side 0 done, both have points (`unproc_side = next_point(0).size > next_point(1).size`, compare
  `ByRatio{P − A}` with `ByRatio{B − A}`, advance both if `B.size == P.size`); after each step
  `is_gt` sets the flag of `unproc_side`, `is_lt` the other, and both flags set returns `unordered`.
  `compareChunks c0 c1 = sweep c0 c1 0 0 false false`.
* `ImprovesFeerateDiagram old new := compareChunks new old = .greater`
  (`std::is_gt(CompareChunks(chunk_results.second, chunk_results.first))`).
* Mathematical side: `diagram cs : ℚ → ℚ`, linear with slope `fee/size` across each chunk in order,
  constant (total fee) after the last; `diagramFee`, `diagramSize`; `SizesPos` (every chunk has
  positive size — `Assume(slope_ap.size > 0)`), `FeeratesNonIncreasing` (`ByRatio` chain);
  `Dominates c0 c1` (∀ x ≥ 0, diagram c1 x ≤ diagram c0 x), `BetterSomewhere c0 c1`
  (∃ x ≥ 0, diagram c1 x < diagram c0 x), `StrictlyBetter = Dominates ∧ BetterSomewhere`.

## Theorems (`Solutions/Sol_BitcoinFeerateDiagram_all.lean`)

| Theorem | Statement |
|---|---|
| `byRatio_eq_compare_ratio` | for positive sizes, `byRatioCmp a b = compare a.ratio b.ratio` (cross-multiplication = ℚ comparison) |
| `byRatio_lt_iff` | `byRatioCmp a b = .lt ↔ a.ratio < b.ratio` |
| `div_round_down_eq_floor` | `div n d true = ⌊n/d⌋` (d > 0) |
| `div_round_up_eq_ceil` | `div n d false = ⌈n/d⌉` (d > 0) |
| `mulFallback_value` | `high * 2^32 + low = a * b` |
| `divFallback_eq_div` | `divFallback (h, l) d rd = div (h * 2^32 + l) d rd` (d > 0) |
| `evaluateFeeDown_eq_floor` | `evaluateFeeDown f s = ⌊fee·s / size⌋` on both code paths |
| `evaluateFeeUp_eq_ceil` | `evaluateFeeUp f s = ⌈fee·s / size⌉` on both code paths |
| `getFee_eq_evaluateFeeUp` | the previous mission's `FeeRate.getFee` is `evaluateFeeUp` |
| `diagram_total` | beyond its total size the diagram equals the total fee |
| `diagram_at_zero` | the diagram starts at (0, 0) |
| `compare_chunks_sound` | for `SizesPos` inputs: `compareChunks c0 c1 = greater ↔ StrictlyBetter c0 c1`, `= less ↔ StrictlyBetter c1 c0`, `= equivalent ↔ diagrams equal on [0,∞)`, `= unordered ↔ BetterSomewhere c0 c1 ∧ BetterSomewhere c1 c0` |
| `improvesFeerateDiagram_iff` | `ImprovesFeerateDiagram old new ↔ StrictlyBetter new old` |
| `diagram_concave` | `SizesPos cs → FeeratesNonIncreasing cs → ConcaveOn ℚ (Icc 0 (diagramSize cs)) (diagram cs)` |
| `improves_total_fee` | `ImprovesFeerateDiagram old new → diagramFee old ≤ diagramFee new` |
| `improves_total_fee_not_strict` | ∃ sorted positive-size `old`, `new` with `ImprovesFeerateDiagram old new` and equal total fee (one chunk (4,2) vs (3,1),(1,1)) |
| `no_free_relay_diagram` | if `diagramFee old = F + totalFee R.evicted`, `diagramFee new = F + R.new.fee`, `ImprovesFeerateDiagram old new` and `PaysForRBF rate R`, then `StrictlyBetter new old ∧ diagramFee old + rate.getFee R.new.vsize ≤ diagramFee new` |

Proof of `compare_chunks_sound`: loop invariant `sweep_spec` (private) — from any reachable state,
the result is `Spec` of "flag set or strictly better somewhere beyond the frontier
`max accum[0].size accum[1].size`", proved by strong induction on the number of unprocessed chunks.
Each step uses that the difference of the two diagrams is affine between consecutive breakpoints of
the union, so its sign on the step interval is decided by its signs at the two ends (the left end
is covered by the flag invariant, the right end by the step's `ByRatio` comparison). Sortedness is
*not* needed for soundness of the sweep — only positive chunk sizes.

Concavity: induction showing that on `(-∞, total size]` the diagram of `c :: cs` is
`min (r·x) (c.fee + diagram cs (x − c.size))` with `r` the first slope, a minimum of concave functions.

## Test vectors (`tests/FeerateDiagramVectors.lean`, compiles with no errors/warnings)

* All 11 `CompareChunks` cases of `rbf_tests.cpp` `feerate_chunks_utilities`, both argument orders
  (19 checks: less/greater/unordered/equivalent, including tail-fee steps), `decide +kernel`.
* `feefrac_tests.cpp`: `+`, `-`, `ByRatio` (incl. empty and oversized) and 40+ `EvaluateFeeDown/Up`
  values (negative fee, oversized, fast-path/`Mul`/`Div` threshold, `INT32_MAX`, issue #32294),
  `decide +kernel`. `ByRatioNegSize` and the `double` paths are not transcribed.
* Hand-computed: diagram values (`#guard`), `ImprovesFeerateDiagram` accept/reject, the equal-fee
  re-chunking example, a fee-increasing but low-feerate replacement that is rejected (unordered),
  empty diagrams, `Div`, `MulFallback`, `DivFallback` values.

## Limits

* The chunk lists are **input**: cluster linearisation and chunking (`cluster_linearize.h`,
  `ChunkLinearization`), `TxGraph` staging, cluster limits (`CalculateChunksForRBF` →
  `UNCALCULABLE`) are not modelled. `GetMainStagingDiagrams`'s sort is captured only as the
  hypothesis `FeeratesNonIncreasing` (needed for concavity, not for `compare_chunks_sound`).
* `no_free_relay_diagram` relates the diagrams to a `Replacement` by hypothesis (old total fee =
  unaffected fee `F` + evicted fees, new total fee = `F` + replacement fee), which is what
  `GetMainStagingDiagrams` yields but is not derived from a mempool model.
* No machine-integer overflow: fees and sizes are `ℤ`, matching the C++ under its documented
  preconditions. Concavity is stated on `[0, total size]`; past the total size the horizontal tail
  is concave only if the last chunk's fee is nonnegative.
