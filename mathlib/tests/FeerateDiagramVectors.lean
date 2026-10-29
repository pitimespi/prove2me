import Definitions.Def_BitcoinFeerateDiagram

/-!
# Test vectors for `BitcoinFeerateDiagram`

* `CompareChunks`: every case of `feerate_chunks_utilities` (`src/test/rbf_tests.cpp`, lines
  485–559, revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`), both argument orders;
* `FeeFrac` arithmetic, `ByRatio` and `EvaluateFeeDown/Up`: the `ByRatio` and `EvaluateFee*` checks of
  `feefrac_operators` (`src/test/feefrac_tests.cpp`, lines 12–155, same revision);
  `ByRatioNegSize` and the double-arithmetic paths are not transcribed and are skipped;
* hand-computed cases: diagram values, the fallback `Mul`/`Div`, `ImprovesFeerateDiagram`.

Kernel-checked with `decide +kernel` (no `native_decide`); values in `ℚ` are checked with `#guard`.
-/

open BitcoinFeerateDiagram

/-! ## `rbf_tests.cpp`, `feerate_chunks_utilities` -/

-- A strictly better case.
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩] [⟨1000, 300⟩, ⟨50, 100⟩] = .less := by decide +kernel
example : compareChunks [⟨1000, 300⟩, ⟨50, 100⟩] [⟨950, 300⟩, ⟨100, 100⟩] = .greater := by decide +kernel
-- Incomparable diagrams.
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩] [⟨1000, 300⟩, ⟨0, 100⟩] = .unordered := by decide +kernel
example : compareChunks [⟨1000, 300⟩, ⟨0, 100⟩] [⟨950, 300⟩, ⟨100, 100⟩] = .unordered := by decide +kernel
-- Strictly better but smaller size.
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩] [⟨1100, 300⟩] = .less := by decide +kernel
example : compareChunks [⟨1100, 300⟩] [⟨950, 300⟩, ⟨100, 100⟩] = .greater := by decide +kernel
-- New diagram strictly better due to the first chunk, the second contributes no fee.
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩] [⟨1100, 100⟩, ⟨0, 100⟩] = .less := by decide +kernel
example : compareChunks [⟨1100, 100⟩, ⟨0, 100⟩] [⟨950, 300⟩, ⟨100, 100⟩] = .greater := by decide +kernel
-- First new chunk better, second worse.
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩] [⟨750, 100⟩, ⟨249, 250⟩, ⟨151, 650⟩] = .unordered := by
  decide +kernel
example : compareChunks [⟨750, 100⟩, ⟨249, 250⟩, ⟨151, 650⟩] [⟨950, 300⟩, ⟨100, 100⟩] = .unordered := by
  decide +kernel
-- Second chunk slightly better: the new diagram wins.
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩] [⟨750, 100⟩, ⟨250, 250⟩, ⟨150, 150⟩] = .less := by
  decide +kernel
example : compareChunks [⟨750, 100⟩, ⟨250, 250⟩, ⟨150, 150⟩] [⟨950, 300⟩, ⟨100, 100⟩] = .greater := by
  decide +kernel
-- Identical diagrams.
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩] [⟨950, 300⟩, ⟨100, 100⟩] = .equivalent := by decide +kernel
-- Same aggregate fee, different total size (single tail-fee check step).
example : compareChunks [⟨950, 300⟩, ⟨100, 99⟩] [⟨950, 300⟩, ⟨100, 100⟩] = .greater := by decide +kernel
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩] [⟨950, 300⟩, ⟨100, 99⟩] = .less := by decide +kernel
-- Multiple tail-fee check steps.
example : compareChunks [⟨950, 300⟩, ⟨100, 99⟩] [⟨950, 300⟩, ⟨100, 100⟩, ⟨0, 1⟩, ⟨0, 1⟩] = .greater := by
  decide +kernel
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩, ⟨0, 1⟩, ⟨0, 1⟩] [⟨950, 300⟩, ⟨100, 99⟩] = .less := by
  decide +kernel
-- Multiple tail-fee check steps, unordered result.
example : compareChunks [⟨950, 300⟩, ⟨100, 99⟩] [⟨950, 300⟩, ⟨100, 100⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩] =
    .unordered := by decide +kernel
example : compareChunks [⟨950, 300⟩, ⟨100, 100⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩] [⟨950, 300⟩, ⟨100, 99⟩] =
    .unordered := by decide +kernel

-- `ImprovesFeerateDiagram old new` is `CompareChunks(new, old) == greater`.
example : ImprovesFeerateDiagram [⟨950, 300⟩, ⟨100, 100⟩] [⟨1000, 300⟩, ⟨50, 100⟩] := by
  unfold ImprovesFeerateDiagram; decide +kernel
example : ¬ ImprovesFeerateDiagram [⟨950, 300⟩, ⟨100, 100⟩] [⟨950, 300⟩, ⟨100, 100⟩] := by
  unfold ImprovesFeerateDiagram; decide +kernel
example : ¬ ImprovesFeerateDiagram [⟨950, 300⟩, ⟨100, 100⟩] [⟨1000, 300⟩, ⟨0, 100⟩] := by
  unfold ImprovesFeerateDiagram; decide +kernel

/-! ## `feefrac_tests.cpp`, `feefrac_operators` -/

-- operators
example : (⟨1000, 100⟩ + ⟨500, 300⟩ : FeeFrac) = ⟨1500, 400⟩ := by decide +kernel
example : (⟨1000, 100⟩ - ⟨500, 300⟩ : FeeFrac) = ⟨500, -200⟩ := by decide +kernel
example : (0 : FeeFrac) = ⟨0, 0⟩ := by decide +kernel
example : (⟨3000, 300⟩ - ⟨2000, 200⟩ : FeeFrac) = ⟨1000, 100⟩ := by decide +kernel
example : (⟨1000, 100⟩ : FeeFrac) ≠ ⟨2000, 200⟩ := by decide +kernel
-- ByRatio
example : FeeFrac.byRatioCmp ⟨1000, 100⟩ ⟨2000, 200⟩ = .eq := by decide +kernel  -- not strictly better
example : FeeFrac.byRatioCmp ⟨1000, 100⟩ ⟨500, 300⟩ = .gt := by decide +kernel
example : FeeFrac.byRatioCmp ⟨500, 300⟩ ⟨1000, 100⟩ = .lt := by decide +kernel
example : FeeFrac.byRatioCmp ⟨1000, 100⟩ 0 = .eq := by decide +kernel  -- "empty" comparisons
example : FeeFrac.byRatioCmp 0 0 = .eq := by decide +kernel
example : FeeFrac.byRatioCmp ⟨4611686000000, 4000000⟩ ⟨184467440000000, 100000⟩ = .lt := by decide +kernel
-- EvaluateFeeDown / EvaluateFeeUp, zero fee
example : FeeFrac.evaluateFeeDown ⟨0, 1⟩ 0x7fffffff = 0 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨0, 1⟩ 1000000 = 0 := by decide +kernel
-- p1 = (1000, 100)
example : FeeFrac.evaluateFeeDown ⟨1000, 100⟩ 1 = 10 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨1000, 100⟩ 0x7fffffff = 0x7fffffff * 10 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨1000, 100⟩ 100000000 = 1000000000 := by decide +kernel
-- neg = (-1001, 100)  (Mul/Div path)
example : FeeFrac.evaluateFeeDown ⟨-1001, 100⟩ 0 = 0 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨-1001, 100⟩ 1 = -11 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨-1001, 100⟩ 2 = -21 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨-1001, 100⟩ 3 = -31 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨-1001, 100⟩ 100 = -1001 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨-1001, 100⟩ 101 = -1012 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨-1001, 100⟩ 100000001 = -1001000011 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨-1001, 100⟩ 0x7fffffff = -21496311307 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨-1001, 100⟩ 1 = -10 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨-1001, 100⟩ 2 = -20 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨-1001, 100⟩ 3 = -30 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨-1001, 100⟩ 100 = -1001 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨-1001, 100⟩ 101 = -1011 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨-1001, 100⟩ 100000001 = -1001000010 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨-1001, 100⟩ 0x7fffffff = -21496311306 := by decide +kernel
-- oversized_1 = (4611686000000, 4000000)  (Mul/Div path)
example : FeeFrac.evaluateFeeDown ⟨4611686000000, 4000000⟩ 1 = 1152921 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨4611686000000, 4000000⟩ 2 = 2305843 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨4611686000000, 4000000⟩ 1548031267 = 1784758530396540 := by
  decide +kernel
example : FeeFrac.evaluateFeeUp ⟨4611686000000, 4000000⟩ 1 = 1152922 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨4611686000000, 4000000⟩ 2 = 2305843 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨4611686000000, 4000000⟩ 1548031267 = 1784758530396541 := by
  decide +kernel
-- threshold between the fast path and Mul/Div
example : FeeFrac.evaluateFeeDown ⟨0x1ffffffff, 123456789⟩ 98765432 = 6871947728 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨0x200000000, 123456789⟩ 98765432 = 6871947729 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨0x200000001, 123456789⟩ 98765432 = 6871947730 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨0x1ffffffff, 123456789⟩ 98765432 = 6871947729 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨0x200000000, 123456789⟩ 98765432 = 6871947730 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨0x200000001, 123456789⟩ 98765432 = 6871947731 := by decide +kernel
-- max_fee = (2100000000000000, INT32_MAX)
example : FeeFrac.evaluateFeeDown ⟨2100000000000000, 0x7fffffff⟩ 1 = 977888 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨2100000000000000, 0x7fffffff⟩ 3 = 2933666 := by decide +kernel
example : FeeFrac.evaluateFeeDown ⟨2100000000000000, 0x7fffffff⟩ 1256796054 = 1229006664189047 := by
  decide +kernel
example : FeeFrac.evaluateFeeDown ⟨2100000000000000, 0x7fffffff⟩ 0x7fffffff = 2100000000000000 := by
  decide +kernel
example : FeeFrac.evaluateFeeUp ⟨2100000000000000, 0x7fffffff⟩ 1 = 977889 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨2100000000000000, 0x7fffffff⟩ 2 = 1955778 := by decide +kernel
example : FeeFrac.evaluateFeeUp ⟨2100000000000000, 0x7fffffff⟩ 1256796054 = 1229006664189048 := by
  decide +kernel
example : FeeFrac.evaluateFeeUp ⟨2100000000000000, 0x7fffffff⟩ 0x7fffffff = 2100000000000000 := by
  decide +kernel
-- issue #32294 (no overflow in the model)
example : FeeFrac.evaluateFeeDown ⟨0x7ffffffdfffffffb, 0x7ffffffd⟩ 0x7fffffff = 0x7fffffffffffffff := by
  decide +kernel

/-! ## Hand-computed cases -/

-- The diagram of `[(950, 300), (100, 100)]`: slope 19/6 up to size 300 (fee 950), then slope 1 up to
-- size 400 (fee 1050), then horizontal.
#guard diagram [⟨950, 300⟩, ⟨100, 100⟩] 0 == 0
#guard diagram [⟨950, 300⟩, ⟨100, 100⟩] 150 == 475
#guard diagram [⟨950, 300⟩, ⟨100, 100⟩] 300 == 950
#guard diagram [⟨950, 300⟩, ⟨100, 100⟩] 350 == 1000
#guard diagram [⟨950, 300⟩, ⟨100, 100⟩] 400 == 1050
#guard diagram [⟨950, 300⟩, ⟨100, 100⟩] 10000 == 1050
#guard diagram [⟨950, 300⟩, ⟨100, 100⟩] 100 == 950 / 3
-- unordered case above: at size 300 the new diagram is higher (1000 > 950), at size 400 lower
-- (1000 < 1050)
#guard diagram [⟨1000, 300⟩, ⟨0, 100⟩] 300 == 1000
#guard diagram [⟨1000, 300⟩, ⟨0, 100⟩] 400 == 1000
-- total fee / total size
#guard diagramFee [⟨750, 100⟩, ⟨250, 250⟩, ⟨150, 150⟩] == 1150
#guard diagramSize [⟨750, 100⟩, ⟨250, 250⟩, ⟨150, 150⟩] == 500

-- Re-chunking the same transactions: one chunk (4, 2) vs chunks (3, 1), (1, 1): strict improvement
-- at equal total fee (the witness of `improves_total_fee_not_strict`).
example : ImprovesFeerateDiagram [⟨4, 2⟩] [⟨3, 1⟩, ⟨1, 1⟩] := by
  unfold ImprovesFeerateDiagram; decide +kernel
example : diagramFee [⟨4, 2⟩] = diagramFee [⟨3, 1⟩, ⟨1, 1⟩] := by decide +kernel
-- A replacement that adds fee but is concentrated at a low feerate is rejected: old chunk (10, 1),
-- new chunk (12, 10).
example : compareChunks [⟨12, 10⟩] [⟨10, 1⟩] = .unordered := by decide +kernel
example : ¬ ImprovesFeerateDiagram [⟨10, 1⟩] [⟨12, 10⟩] := by
  unfold ImprovesFeerateDiagram; decide +kernel
-- The empty diagrams.
example : compareChunks [] [] = .equivalent := by decide +kernel
example : compareChunks [⟨1, 1⟩] [] = .greater := by decide +kernel
example : compareChunks [⟨0, 1⟩] [] = .equivalent := by decide +kernel
example : compareChunks [⟨-1, 1⟩] [] = .less := by decide +kernel

-- `Div` / `DivFallback` / `MulFallback`
example : FeeFrac.div (-7) 2 true = -4 := by decide +kernel
example : FeeFrac.div (-7) 2 false = -3 := by decide +kernel
example : FeeFrac.div 7 2 true = 3 := by decide +kernel
example : FeeFrac.div 7 2 false = 4 := by decide +kernel
example : FeeFrac.mulFallback 0x7ffffffdfffffffb 0x7fffffff =
    (0x3ffffffe7fffffff, 0x80000005) := by decide +kernel
example : (FeeFrac.mulFallback (-1001) 0x7fffffff).1 * 2 ^ 32 + (FeeFrac.mulFallback (-1001) 0x7fffffff).2 =
    -1001 * 0x7fffffff := by decide +kernel
example : FeeFrac.divFallback (FeeFrac.mulFallback (-1001) 0x7fffffff) 100 true = -21496311307 := by
  decide +kernel
example : FeeFrac.divFallback (FeeFrac.mulFallback (-1001) 0x7fffffff) 100 false = -21496311306 := by
  decide +kernel
example : FeeFrac.divFallback (FeeFrac.mulFallback 0x7ffffffdfffffffb 0x7fffffff) 0x7ffffffd true =
    0x7fffffffffffffff := by decide +kernel
