SRC = ("Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, "
       "operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), "
       "policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; "
       "test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp")
TAGS = ["bitcoin", "mempool", "rbf", "cluster-mempool", "feerate-diagram", "policy", "feefrac", "formal-verification", "mathlib"]

DEFINITION = {
    "definition_name": "BitcoinFeerateDiagram",
    "definition_title": "FeeFrac arithmetic, Core's chunk-diagram comparison, and the cluster-mempool replacement check",
    "natural_language_statement": r"""A transcription of the cluster mempool's replacement check over the replace-by-fee mission's `BitcoinReplacement`, at Bitcoin Core revision `a773e1e`, where it replaced BIP125 rule 3.

**`FeeFrac`** — a fee and a size (integers). **`IsEmpty`**, **`mul`**, **`mulFallback`** (the 32-bit split multiplication), **`div`** (round down or up), **`divFallback`**, **`ceilDiv`**, **`evaluateFee`**, **`evaluateFeeDown`**, **`evaluateFeeUp`** — Core's arithmetic, with both code paths. **`byRatioCmp a b`** — `compare (a.fee · b.size) (b.fee · a.size)`, the `ByRatio` ordering; **`ratio a`** — `fee / size` in $\mathbb{Q}$.

**`PartialOrdering`** — `less`, `equivalent`, `greater`, `unordered`; **`boolCompare`**. **`sweep`** — the loop of `CompareChunks`, one equation per iteration over the two chunk lists with the accumulated (fee, size) of each and the two "better somewhere" flags; **`compareChunks c0 c1`** — Core's `CompareChunks`. **`ImprovesFeerateDiagram old new`** — `compareChunks new old = greater` (`policy/rbf.cpp`).

**`diagram cs x`** — the feerate diagram as a function: the cumulative fee at cumulative size $x$, linear within each chunk and constant after the last; **`diagramFee`**, **`diagramSize`** — totals. **`SizesPos`** — every chunk has positive size; **`FeeratesNonIncreasing`** — chunk feerates in non-increasing order. **`Dominates c0 c1`** — `diagram c0 ≥ diagram c1` on $[0, \infty)$; **`BetterSomewhere c0 c1`** — strictly greater at some $x \ge 0$; **`StrictlyBetter`** — both.

**Formalization Note.** Imports Mathlib and the replacement mission. The chunk lists (the linearization of the affected clusters, `txmempool.cpp`/`txgraph.cpp`) are taken as input; fees and sizes are unbounded integers, so overflow is not modelled.""",
}

T = {}
T["byRatio_eq_compare_ratio"] = ("Core's cross-multiplied fee-rate comparison is the comparison of exact ratios", r"""For positive sizes: `byRatioCmp a b = compare (ratio a) (ratio b)`.""")
T["byRatio_lt_iff"] = ("ByRatio less-than is the rational less-than", r"""For positive sizes: `byRatioCmp a b = .lt ↔ ratio a < ratio b`.""")
T["div_round_down_eq_floor"] = ("Div rounding down is the floor", r"""For $d > 0$: `div n d true = ⌊n/d⌋`.""")
T["div_round_up_eq_ceil"] = ("Div rounding up is the ceiling", r"""For $d > 0$: `div n d false = ⌈n/d⌉`.""")
T["mulFallback_value"] = ("The split multiplication computes the product", r"""`(mulFallback a b).1 · 2^32 + (mulFallback a b).2 = a · b`.""")
T["divFallback_eq_div"] = ("The split division agrees with Div", r"""For $d > 0$: `divFallback (h, l) d rd = div (h · 2^32 + l) d rd`.""")
T["evaluateFeeDown_eq_floor"] = ("EvaluateFeeDown is the floor of fee·size/size, on both code paths", r"""For positive size and non-negative `atSize`: `evaluateFeeDown f atSize = ⌊fee · atSize / size⌋`.""")
T["evaluateFeeUp_eq_ceil"] = ("EvaluateFeeUp is the ceiling, on both code paths", r"""As above with the ceiling.""")
T["getFee_eq_evaluateFeeUp"] = ("The replacement mission's GetFee is EvaluateFeeUp", r"""`r.getFee v = evaluateFeeUp ⟨r.fee, r.size⟩ v`, linking the two missions' fee arithmetic.""")
T["diagram_total"] = ("Past its total size the diagram is the total fee", r"""For positive chunk sizes and $x \ge$ `diagramSize cs`: `diagram cs x = diagramFee cs`.""")
T["diagram_at_zero"] = ("The diagram starts at the origin", r"""For positive chunk sizes: `diagram cs 0 = 0`.""")
T["compare_chunks_sound"] = ("Core's CompareChunks sweep decides the pointwise comparison of the two feerate diagrams", r"""For chunk lists with positive sizes: `compareChunks c0 c1` is `greater` iff `StrictlyBetter c0 c1` (never below, strictly above somewhere); `less` iff `StrictlyBetter c1 c0`; `equivalent` iff the diagrams are equal on $[0, \infty)$; `unordered` iff each is strictly above the other somewhere. The C++ sweep over breakpoints computes exactly the mathematical comparison of the two piecewise-linear functions; sorted feerates are not needed.""")
T["improvesFeerateDiagram_iff"] = ("ImprovesFeerateDiagram means a strictly better diagram", r"""For positive sizes: `ImprovesFeerateDiagram old new ↔ StrictlyBetter new old`.""")
T["diagram_concave"] = ("A chunking with non-increasing feerates has a concave diagram", r"""For positive sizes and non-increasing feerates, `diagram cs` is concave on $[0, \text{diagramSize}]$.""")
T["improves_total_fee"] = ("A strict improvement does not lower the total fee", r"""For positive sizes: `ImprovesFeerateDiagram old new → diagramFee old ≤ diagramFee new`.""")
T["improves_total_fee_not_strict"] = ("A strict improvement may keep the total fee", r"""There are sorted, positive-size chunkings with `ImprovesFeerateDiagram old new` and equal total fees (one chunk (4, 2) against (3, 1), (1, 1)): the diagram check alone does not make the replacement pay more; `PaysForRBF` does.""")
T["no_free_relay_diagram"] = ("No free relay under the cluster-mempool rules", r"""If the old and new diagrams' totals are a common $F$ plus the evicted fees and plus the replacement's fee, and both `ImprovesFeerateDiagram` and the replacement mission's `PaysForRBF rate R` hold: the new diagram is strictly better and its total fee exceeds the old by at least `rate.getFee R.new.vsize`. The replacement mission's no-free-relay theorems therefore hold at the pinned revision's actual rules.""")
THEOREMS = {f"BitcoinFeerateDiagram.{k}": dict(title=v[0], nl=v[1], ms=None) for k, v in T.items()}
THEOREMS["BitcoinFeerateDiagram.compare_chunks_sound"]["ms"] = ("The sweep is the pointwise comparison", "A loop invariant for `sweep` relating the accumulated points to the two diagrams at every breakpoint.")
ORDER = ["BitcoinFeerateDiagram." + k for k in ["byRatio_eq_compare_ratio", "byRatio_lt_iff", "div_round_down_eq_floor", "div_round_up_eq_ceil",
  "mulFallback_value", "divFallback_eq_div", "evaluateFeeDown_eq_floor", "evaluateFeeUp_eq_ceil", "getFee_eq_evaluateFeeUp", "diagram_total",
  "diagram_at_zero", "compare_chunks_sound", "improvesFeerateDiagram_iff", "diagram_concave", "improves_total_fee", "improves_total_fee_not_strict",
  "no_free_relay_diagram"]]
