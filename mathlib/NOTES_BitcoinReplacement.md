# NOTES — `BitcoinReplacement`: what Bitcoin Core's RBF fee rules guarantee

Files: `Definitions/Def_BitcoinReplacement.lean` (model), `Solutions/Sol_BitcoinReplacement_all.lean`
(proofs, 15 public theorems, no `sorry`, axioms ⊆ {propext, Classical.choice, Quot.sound}).

Source read as data: `policy/rbf.cpp`, `policy/rbf.h`, `policy/feerate.h`, `policy/feerate.cpp`,
`policy/policy.cpp` at bitcoin/bitcoin revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, plus
`util/feefrac.h` and `policy/policy.h` at the same revision (fetched from GitHub) for `EvaluateFeeUp`,
`ByRatio` and `DEFAULT_INCREMENTAL_RELAY_FEE`.

## The model (abstract mempool, no scripts, no inputs)

* `Tx = {fee : ℕ, vsize : ℕ, 0 < vsize}` — satoshi (modified) fee and virtual size.
* `FeeRate = {fee : ℕ, size : ℕ, 0 < size}` — Core's `FeePerVSize`; `FeeRate.perKvB k = ⟨k, 1000⟩`
  is `CFeeRate(k)`; `defaultIncrementalRelayFee = perKvB 100`.
* `FeeRate.getFee r v = (r.fee * v + (r.size - 1)) / r.size = ⌈r.fee·v / r.size⌉`.
* `Tx.feeRate t = ⟨t.fee, t.vsize⟩` (exact, no rounding: `CFeeRate(nFeePaid, vsize)` with `vsize > 0`
  stores `FeePerVSize(nFeePaid, vsize)` losslessly at this revision).
* `FeeRate.lt a b ↔ a.fee * b.size < b.fee * a.size` — exactly `ByRatio::operator<`.
* `Replacement = {new : Tx, evicted : Multiset Tx, direct : Multiset Tx, direct ≤ evicted}`;
  `evicted` plays `all_conflicts` (direct conflicts + all descendants, as `GetEntriesForConflicts`
  collects them), `direct` plays `iters_conflicting`. Multisets (not sets) so that distinct entries
  with equal (fee, vsize) are not merged. `totalFee s = Σ fee`.
* `IsChain rate t₀ [R₁,…,Rₙ]`: each `Rᵢ` is `Valid`, `R₁` evicts `t₀`, `Rᵢ₊₁` evicts `Rᵢ.new`;
  `chainEnd t₀ Rs = tₙ`; `chainVsizes Rs = [vsize t₁, …, vsize tₙ]`.

## Exact transcription of the two fee rules

### `PaysForRBF` (revision `a773e1e`, `policy/rbf.cpp`) — transcribed verbatim

```cpp
if (replacement_fees < original_fees) return "... less fees than conflicting txs";   // "Rule #3" in the comment
CAmount additional_fees = replacement_fees - original_fees;
if (additional_fees < relay_fee.GetFee(replacement_vsize)) return "... not enough additional fees to relay"; // Rule #4
```
with `original_fees = Σ_{all_conflicts} GetModifiedFee`, `replacement_fees` = the replacement's
modified fee, `replacement_vsize` = its vsize, `relay_fee` = the node's incremental relay feerate
(`-incrementalrelayfee`, default `DEFAULT_INCREMENTAL_RELAY_FEE{100}` sat/kvB at this revision;
it was 1000 sat/kvB = 1 sat/vB up to v29 — the brief's "default 1 sat/vbyte" is the pre-#33106 value).

```lean
def PaysForRBF (rate : FeeRate) (R : Replacement) : Prop :=
  totalFee R.evicted ≤ R.new.fee ∧ rate.getFee R.new.vsize ≤ R.new.fee - totalFee R.evicted
```
ℕ truncated subtraction is faithful because the C++ subtraction is only reached after the first
check.  `paysForRBF_iff` shows this is equivalent to `totalFee evicted + getFee vsize ≤ new.fee`.

`CFeeRate::GetFee(v)` at this revision is `FeePerVSize::EvaluateFeeUp(v)` =
`CeilDiv(uint64_t(fee) * v, uint32_t(size))` for `0 ≤ fee < 2^33` (else the 128-bit `Div(Mul(fee,v),
size, RoundDown=false)`, same mathematical value), i.e. **`⌈fee·v/size⌉`, rounded up**.  The two
special cases of `GetFee` (`IsEmpty()` ⇒ 0; negative fee ⇒ −1) are unreachable for a positive-size
nonnegative rate and are not modelled (the model requires `size > 0`, `fee ≥ 0`).  Note: this is
**not** the old `nSatoshisPerK * nSize / 1000` arithmetic the brief describes; at `a773e1e`
`CFeeRate` is an exact fraction (`FeePerVSize`), and the old v29 `GetFee` (`std::ceil(nSatoshisPerK
* nSize / 1000.0)` with a floor of 1 sat) agrees with the ceiling here for rates given in sat/kvB.
The ℕ formula was checked by `#eval` against the C++ semantics (`perKvB 100` gives
`getFee = [0,1,1,…,1,2,…]` = ⌈v/10⌉; `perKvB 1000` gives `getFee v = v`).

### `PaysMoreThanConflicts` (BIP125 rule 3) — **not present at `a773e1e`**

At revision `a773e1e` `policy/rbf.{h,cpp}` contain no `PaysMoreThanConflicts`: the cluster-mempool
series replaced the per-conflict feerate rule with `ImprovesFeerateDiagram` (the replacement must
strictly improve the mempool's feerate diagram, computed by `ChangeSet::CalculateChunksForRBF` /
`CompareChunks`).  That check depends on cluster linearisation and is out of scope here.  The model
transcribes rule 3 from the last form in which it existed in `policy/rbf.cpp` (tag `v29.0`):

```cpp
for (const auto& mi : iters_conflicting) {
    CFeeRate original_feerate(mi->GetModifiedFee(), mi->GetTxSize());
    if (replacement_feerate <= original_feerate) return "... new feerate <= old feerate";
}
```
```lean
def PaysMoreThanConflicts (R : Replacement) : Prop := ∀ t ∈ R.direct, FeeRate.lt t.feeRate R.new.feeRate
```
with `<=` on `CFeeRate` evaluated as `ByRatio` cross-multiplication (the `a773e1e` comparison; in
v29 `CFeeRate` compared the rounded-down `nSatoshisPerK = fee*1000/vsize` values instead — the model
uses the exact comparison, which is the one in force for every `CFeeRate` comparison at `a773e1e`).
`Valid rate R := PaysMoreThanConflicts R ∧ PaysForRBF rate R`.  Only the theorems named
`evicted_feerate_dominated`, `feeRateQ_lt_iff`, `min_direct_feerate_lt` use rule 3; all the
fee/bandwidth/pinning theorems use `PaysForRBF` alone (they hold under `ImprovesFeerateDiagram` too,
since that check is additional).

## Public theorems (all fully proved)

| name | statement |
|---|---|
| `fee_strictly_increases` | `0 < rate.fee → Valid rate R → t ∈ R.evicted → t.fee < R.new.fee` |
| `paysForRBF_iff` | `PaysForRBF rate R ↔ totalFee R.evicted + rate.getFee R.new.vsize ≤ R.new.fee` |
| `bandwidth_paid` | `IsChain rate t₀ Rs → t₀.fee + Σᵢ rate.getFee (vsize tᵢ) ≤ fee tₙ` |
| `bandwidth_paid_total` | `… → t₀.fee + rate.getFee (Σᵢ vsize tᵢ) ≤ fee tₙ` (ceiling is subadditive) |
| `bandwidth_paid_rate` | `… → t₀.fee·size + fee·Σᵢ vsize tᵢ ≤ fee tₙ · size` (no rounding, in ℕ) |
| `bandwidth_paid_real` | `… → (t₀.fee : ℚ) + (fee/size)·Σᵢ vsize tᵢ ≤ fee tₙ` |
| `replacement_count_bound_min_vsize` | `… → (∀ R ∈ Rs, m ≤ vsize R.new) → t₀.fee + n·getFee m ≤ fee tₙ` |
| `replacement_count_bound` | `… → t₀.fee + n·rate.getFee 1 ≤ fee tₙ` |
| `replacement_count_le_fee` | `0 < rate.fee → … → t₀.fee + n ≤ fee tₙ` |
| `replacement_count_bound_rate` | `… → n·rate.fee ≤ (fee tₙ − t₀.fee)·rate.size`, i.e. `n ≤ (fee tₙ − fee t₀)/r` |
| `pinning_cost` | `Valid rate R → t ::ₘ D ≤ R.evicted → t.fee + totalFee D + rate.getFee R.new.vsize ≤ R.new.fee` |
| `pinning_cost_tight` | `R.evicted = t ::ₘ D → (PaysForRBF rate R ↔ t.fee + totalFee D + getFee vsize ≤ R.new.fee)` |
| `evicted_feerate_dominated` | `Valid rate R → t ∈ R.direct → t.fee·vsize new < new.fee·vsize t` |
| `feeRateQ_lt_iff` | `a.feeRateQ < b.feeRateQ ↔ FeeRate.lt a.feeRate b.feeRate` (ByRatio = exact fraction order) |
| `min_direct_feerate_lt` | `Valid rate R → R.direct ≠ 0 → ∃ t ∈ R.direct, (∀ s ∈ R.direct, t.feeRateQ ≤ s.feeRateQ) ∧ t.feeRateQ < new.feeRateQ` |

Here `n = Rs.length`, `tₙ = chainEnd t₀ Rs`, `r = rate.fee / rate.size` sat/vB.

Remarks on the brief's statements and rounding:
* Theorem 2 is proved in the `GetFee` form (`bandwidth_paid`), and the "cleaner" rate form follows
  *without* loss: since `GetFee` rounds **up**, `Σ GetFee(vᵢ) ≥ GetFee(Σ vᵢ) ≥ r·Σ vᵢ`, so the exact
  inequality `fee(tₙ) ≥ fee(t₀) + r·Σ vsize(tᵢ)` holds (`bandwidth_paid_rate`/`_real`).  No corrected
  statement was needed.
* Theorem 3, "fee(tₙ) ≥ n·rate": true in the form `n·r ≤ fee(tₙ) − fee(t₀)` (`replacement_count_bound_rate`,
  using vsize ≥ 1 per replacement) and `n ≤ fee(tₙ) − fee(t₀)` for any positive rate (because
  `GetFee(v) ≥ 1` whenever `rate.fee > 0` and `v > 0`, by the round-up).  With a zero rate
  (`-incrementalrelayfee=0`) nothing bounds `n` except `fee(tₙ) ≥ fee(t₀)`; hence the `0 < rate.fee`
  hypothesis on `fee_strictly_increases` and `replacement_count_le_fee`.  A realistic sharper bound uses
  the minimum standard size (`MIN_STANDARD_TX_NONWITNESS_SIZE = 65`) via `replacement_count_bound_min_vsize`.
* Theorem 1 needs `0 < rate.fee` for the same reason; with rate 0 a replacement may pay exactly the
  evicted total, so it is not strictly more than a single evicted tx when that tx is the only one.
* Theorem 4 (`pinning_cost`) is stated for an arbitrary multiset `D` of descendants with `t ::ₘ D ≤
  evicted`, and `pinning_cost_tight` shows the bound is exactly rule 4 when `evicted = t ::ₘ D`, so
  attaching descendants of total fee `F` raises the rule-4 cost of replacing `t` by exactly `F`.
* Theorem 5's corollary is stated existentially (there is a minimal-feerate direct conflict and it is
  dominated), because the ByRatio order is a total preorder, not a `Multiset.inf` on ℚ.

## Hypotheses / scope (honest limits)

* **Fees are modified fees** (`prioritisetransaction`); the model has one `fee` per tx.
* **Structural rules are not modelled**: rule 2 (no new unconfirmed inputs, `EntriesAndTxidsDisjoint`
  + `HasNoNewUnconfirmed`), rule 5 (`MAX_REPLACEMENT_CANDIDATES = 100` — at `a773e1e` a bound on the
  number of *distinct clusters* touched, no longer on the number of evicted entries), opt-in
  signalling (`IsRBFOptIn`; full-RBF nodes ignore it), and `ImprovesFeerateDiagram`.  None of them is
  needed for the fee theorems, which are proved from `PaysForRBF` (and `PaysMoreThanConflicts` for
  theorem 5) alone; adding them as hypotheses only shrinks the set of valid replacements.
* The eviction multiset is given, not computed: descendants, conflicts-by-input and the mempool graph
  are abstracted away, so "`t ::ₘ D ≤ evicted`" is a hypothesis, not derived from topology.
* **No package / descendant relay, no v3/TRUC, no sibling eviction, no ephemeral-anchor rules, no
  cluster mempool linearisation.**  The chain theorems assume each link is a plain single-tx
  replacement checked by `PaysForRBF`; package RBF (`PackageMempoolChecks`) sums fees/vsizes over the
  package and is not modelled.
* `GetFee` is modelled only on its nonnegative, positive-size branch; overflow (int64/int128) is not
  modelled (ℕ is unbounded).
* Rule 3 is the v29 `PaysMoreThanConflicts` with the `a773e1e` exact `ByRatio` comparison (the v29
  binary compared rounded-down sat/kvB values, which differs in edge cases); it is **absent** from
  `a773e1e` itself.  The brief asked to transcribe it from `rbf.cpp` at `a773e1e`, which is not
  possible — this is the one place where the model deliberately departs from that revision, and is
  the only ingredient of `evicted_feerate_dominated` / `min_direct_feerate_lt`.

## Literature

The statements are the standard "no free relay" and "pinning" readings of BIP125 (D. Harding,
P. Todd, *Opt-in Full Replace-by-Fee Signaling*, BIP 125, 2015: rules 3–4) and of Bitcoin Core's
`doc/policy/mempool-replacements.md` ("the replacement must pay for its own bandwidth at or above the
incremental relay feerate … bounds the number of times a transaction can be replaced"); the pinning
observation (attaching high-fee or large descendants raises the absolute fee a replacement must pay)
is as described in Gloria Zhao's *Pinning* notes and `doc/policy/packages.md`.  Nothing here is new
mathematics; the value is the exact rounding-aware statement and the machine-checked derivation.
