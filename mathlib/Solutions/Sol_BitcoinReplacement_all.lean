import Definitions.Def_BitcoinReplacement

open BitcoinReplacement

/-! ## Arithmetic of `CFeeRate::GetFee` (ceiling division) -/

/-- `GetFee v ≤ n` iff `fee · v ≤ n · size`: `getFee` is the least `n` with `fee·v ≤ n·size`. -/
private theorem getFee_le_iff (r : FeeRate) (v n : ℕ) :
    r.getFee v ≤ n ↔ r.fee * v ≤ n * r.size := by
  unfold FeeRate.getFee
  have hs := r.size_pos
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hs, Nat.succ_mul]
  omega

private theorem le_getFee_mul (r : FeeRate) (v : ℕ) : r.fee * v ≤ r.getFee v * r.size :=
  (getFee_le_iff r v _).1 le_rfl

private theorem getFee_pos (r : FeeRate) (hr : 0 < r.fee) {v : ℕ} (hv : 0 < v) :
    1 ≤ r.getFee v := by
  by_contra h
  have h0 : r.getFee v ≤ 0 := by omega
  rw [getFee_le_iff, zero_mul] at h0
  have := Nat.mul_pos hr hv
  omega

private theorem getFee_zero (r : FeeRate) : r.getFee 0 = 0 := by
  have := (getFee_le_iff r 0 0).2 (by simp)
  omega

private theorem getFee_add_le (r : FeeRate) (a b : ℕ) :
    r.getFee (a + b) ≤ r.getFee a + r.getFee b := by
  rw [getFee_le_iff, mul_add, add_mul]
  exact Nat.add_le_add (le_getFee_mul r a) (le_getFee_mul r b)

private theorem getFee_mono (r : FeeRate) {a b : ℕ} (h : a ≤ b) : r.getFee a ≤ r.getFee b := by
  rw [getFee_le_iff]
  exact (Nat.mul_le_mul_left _ h).trans (le_getFee_mul r b)

private theorem getFee_sum_le (r : FeeRate) : ∀ l : List ℕ, r.getFee l.sum ≤ (l.map r.getFee).sum
  | [] => by simp [getFee_zero]
  | x :: l => by
    simp only [List.sum_cons, List.map_cons]
    exact (getFee_add_le r x l.sum).trans (Nat.add_le_add_left (getFee_sum_le r l) _)

private theorem length_mul_getFee_le (r : FeeRate) (m : ℕ) :
    ∀ l : List ℕ, (∀ x ∈ l, m ≤ x) → l.length * r.getFee m ≤ (l.map r.getFee).sum
  | [], _ => by simp
  | x :: l, h => by
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    have h1 := getFee_mono r (h x (List.mem_cons_self ..))
    have h2 := length_mul_getFee_le r m l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

/-! ## Multiset fee sums -/

private theorem fee_le_totalFee {t : Tx} {s : Multiset Tx} (h : t ∈ s) : t.fee ≤ totalFee s :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Tx.fee h)

private theorem totalFee_le_of_le {s u : Multiset Tx} (h : s ≤ u) : totalFee s ≤ totalFee u := by
  obtain ⟨w, rfl⟩ := Multiset.le_iff_exists_add.1 h
  simp [totalFee, Multiset.map_add, Multiset.sum_add]

private theorem totalFee_cons (t : Tx) (D : Multiset Tx) :
    totalFee (t ::ₘ D) = t.fee + totalFee D := by
  simp [totalFee, Multiset.map_cons, Multiset.sum_cons]

/-! ## Chains -/

private theorem chain_bound (rate : FeeRate) :
    ∀ (Rs : List Replacement) (t₀ : Tx), IsChain rate t₀ Rs →
      t₀.fee + ((chainVsizes Rs).map rate.getFee).sum ≤ (chainEnd t₀ Rs).fee
  | [], t₀, _ => by simp [chainVsizes, chainEnd]
  | R :: Rs, t₀, ⟨hv, ht, hc⟩ => by
    have ih := chain_bound rate Rs R.new hc
    have h1 : t₀.fee + rate.getFee R.new.vsize ≤ R.new.fee := by
      have := fee_le_totalFee ht
      have := hv.2.1
      have := hv.2.2
      omega
    simp only [chainVsizes, List.map_cons, List.sum_cons, chainEnd, List.foldl_cons] at ih ⊢
    omega

private theorem chainVsizes_pos (Rs : List Replacement) : ∀ x ∈ chainVsizes Rs, 1 ≤ x := by
  intro x hx
  obtain ⟨R, -, rfl⟩ := List.mem_map.1 hx
  exact R.new.vsize_pos

private theorem feeRateQ_lt_iff' (a b : Tx) :
    a.feeRateQ < b.feeRateQ ↔ a.fee * b.vsize < b.fee * a.vsize := by
  unfold Tx.feeRateQ
  rw [div_lt_div_iff₀ (by exact_mod_cast a.vsize_pos) (by exact_mod_cast b.vsize_pos)]
  exact_mod_cast Iff.rfl

/-! ## Public theorems -/

/-- **Rule 4 ⇒ strict fee increase.**  If the incremental relay fee rate is positive, a valid
replacement pays strictly more than *every single* transaction it evicts (direct conflicts and
their descendants alike): `GetFee(vsize) ≥ 1` once `fee > 0` and `vsize > 0`, so
`new.fee ≥ Σ evicted fees + 1 > fee(t)`. -/
theorem BitcoinReplacement.fee_strictly_increases (rate : BitcoinReplacement.FeeRate)
    (hr : 0 < rate.fee) (R : BitcoinReplacement.Replacement)
    (hR : BitcoinReplacement.Valid rate R) (t : BitcoinReplacement.Tx) (ht : t ∈ R.evicted) :
    t.fee < R.new.fee := by
  have h1 := fee_le_totalFee ht
  have h2 := getFee_pos rate hr R.new.vsize_pos
  have := hR.2.1
  have := hR.2.2
  omega

/-- **Rule 4 exactly.**  `PaysForRBF` holds iff the replacement fee is at least the evicted fees
plus `GetFee(replacement vsize)`; this is the precise cost of a replacement under the fee rules. -/
theorem BitcoinReplacement.paysForRBF_iff (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) :
    BitcoinReplacement.PaysForRBF rate R ↔
      BitcoinReplacement.totalFee R.evicted + rate.getFee R.new.vsize ≤ R.new.fee := by
  unfold BitcoinReplacement.PaysForRBF
  omega

/-- **No free relay (per-replacement `GetFee` form).**  Along a chain of valid replacements
`t₀ ← t₁ ← ⋯ ← tₙ`, the final fee covers the initial fee plus `GetFee(vsize(tᵢ))` for every
relayed replacement `tᵢ`, `i = 1..n`. -/
theorem BitcoinReplacement.bandwidth_paid (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + ((BitcoinReplacement.chainVsizes Rs).map rate.getFee).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee :=
  chain_bound rate Rs t₀ h

/-- **No free relay (aggregate `GetFee` form).**  Because the ceiling is subadditive,
`Σ GetFee(vsize(tᵢ)) ≥ GetFee(Σ vsize(tᵢ))`, so the final fee also pays, at the incremental rate,
for the total number of vbytes relayed across the whole chain. -/
theorem BitcoinReplacement.bandwidth_paid_total (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + rate.getFee (BitcoinReplacement.chainVsizes Rs).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee :=
  (Nat.add_le_add_left (getFee_sum_le rate _) _).trans (chain_bound rate Rs t₀ h)

/-- **No free relay (exact-rate form, in ℕ).**  Cross-multiplied by the rate's denominator:
`fee(t₀)·size + fee·Σ vsize(tᵢ) ≤ fee(tₙ)·size`, i.e. `fee(tₙ) ≥ fee(t₀) + (fee/size)·Σ vsize(tᵢ)`
without any rounding. -/
theorem BitcoinReplacement.bandwidth_paid_rate (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee * rate.size + rate.fee * (BitcoinReplacement.chainVsizes Rs).sum ≤
      (BitcoinReplacement.chainEnd t₀ Rs).fee * rate.size := by
  have h1 := Nat.mul_le_mul_right rate.size (BitcoinReplacement.bandwidth_paid_total rate t₀ Rs h)
  have h2 := le_getFee_mul rate (BitcoinReplacement.chainVsizes Rs).sum
  rw [add_mul] at h1
  omega

/-- **No free relay (exact-rate form, in ℚ).**  `fee(tₙ) ≥ fee(t₀) + r · Σ vsize(tᵢ)` where
`r = fee/size` is the incremental relay fee rate in satoshi per vbyte. -/
theorem BitcoinReplacement.bandwidth_paid_real (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    (t₀.fee : ℚ) + ((rate.fee : ℚ) / rate.size) * (BitcoinReplacement.chainVsizes Rs).sum ≤
      ((BitcoinReplacement.chainEnd t₀ Rs).fee : ℚ) := by
  have hs : (0 : ℚ) < rate.size := by exact_mod_cast rate.size_pos
  have h1 := BitcoinReplacement.bandwidth_paid_rate rate t₀ Rs h
  have h2 : ((t₀.fee * rate.size + rate.fee * (BitcoinReplacement.chainVsizes Rs).sum : ℕ) : ℚ) ≤
      (((BitcoinReplacement.chainEnd t₀ Rs).fee * rate.size : ℕ) : ℚ) := by exact_mod_cast h1
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul] at h2
  rw [div_mul_eq_mul_div, ← le_sub_iff_add_le', div_le_iff₀ hs]
  linarith

/-- **Replacement count bound (general).**  If every replacement in the chain has virtual size at
least `m`, then `fee(tₙ) ≥ fee(t₀) + n · GetFee(m)`. -/
theorem BitcoinReplacement.replacement_count_bound_min_vsize (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) (m : ℕ) (hm : ∀ R ∈ Rs, m ≤ R.new.vsize) :
    t₀.fee + Rs.length * rate.getFee m ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by
  have h1 := chain_bound rate Rs t₀ h
  have h2 := length_mul_getFee_le rate m (BitcoinReplacement.chainVsizes Rs) (by
    intro x hx
    obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx
    exact hm R hR)
  have h3 : (BitcoinReplacement.chainVsizes Rs).length = Rs.length := List.length_map ..
  rw [h3] at h2
  omega

/-- **Replacement count bound.**  A chain of `n` valid replacements starting from `t₀` ends at a
transaction paying `fee(tₙ) ≥ fee(t₀) + n · GetFee(1)`; with any positive incremental rate
`GetFee(1) = 1`, so `n ≤ fee(tₙ) − fee(t₀)`. -/
theorem BitcoinReplacement.replacement_count_bound (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + Rs.length * rate.getFee 1 ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee :=
  BitcoinReplacement.replacement_count_bound_min_vsize rate t₀ Rs h 1
    (fun R _ => R.new.vsize_pos)

/-- **Replacement count bound (positive rate).**  With a positive incremental relay fee rate, the
number of replacements the network can be made to relay is at most the fee the final transaction
pays over the original: `n ≤ fee(tₙ) − fee(t₀) ≤ fee(tₙ)`. -/
theorem BitcoinReplacement.replacement_count_le_fee (rate : BitcoinReplacement.FeeRate)
    (hr : 0 < rate.fee) (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    t₀.fee + Rs.length ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by
  have h1 := BitcoinReplacement.replacement_count_bound rate t₀ Rs h
  have h2 := getFee_pos rate hr Nat.one_pos
  have h3 : Rs.length * 1 ≤ Rs.length * rate.getFee 1 := Nat.mul_le_mul_left _ h2
  omega

/-- **Replacement count bound (exact rate).**  `n · fee ≤ (fee(tₙ) − fee(t₀)) · size`, i.e.
`n ≤ (fee(tₙ) − fee(t₀)) / r` for the incremental rate `r = fee/size` in sat/vB: each replacement
is at least one vbyte and every vbyte is paid for at rate `r`. -/
theorem BitcoinReplacement.replacement_count_bound_rate (rate : BitcoinReplacement.FeeRate)
    (t₀ : BitcoinReplacement.Tx) (Rs : List BitcoinReplacement.Replacement)
    (h : BitcoinReplacement.IsChain rate t₀ Rs) :
    Rs.length * rate.fee ≤ ((BitcoinReplacement.chainEnd t₀ Rs).fee - t₀.fee) * rate.size := by
  have h1 := BitcoinReplacement.bandwidth_paid_rate rate t₀ Rs h
  have h2 := length_mul_getFee_le rate 1 (BitcoinReplacement.chainVsizes Rs) (chainVsizes_pos Rs)
  have h3 : (BitcoinReplacement.chainVsizes Rs).length = Rs.length := List.length_map ..
  -- Σ vsize ≥ n, since every vsize ≥ 1
  have h4 : Rs.length ≤ (BitcoinReplacement.chainVsizes Rs).sum := by
    rw [← h3]
    exact List.length_le_sum_of_one_le _ (chainVsizes_pos Rs)
  have h5 : Rs.length * rate.fee ≤ rate.fee * (BitcoinReplacement.chainVsizes Rs).sum := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ h4
  have h6 : t₀.fee ≤ (BitcoinReplacement.chainEnd t₀ Rs).fee := by
    have := chain_bound rate Rs t₀ h
    omega
  have h7 : ((BitcoinReplacement.chainEnd t₀ Rs).fee - t₀.fee) * rate.size =
      (BitcoinReplacement.chainEnd t₀ Rs).fee * rate.size - t₀.fee * rate.size :=
    Nat.sub_mul ..
  omega

/-- **Pinning cost.**  For every transaction `t`, every multiset `D` of descendants attached to it
(by anyone), and every valid replacement `R` whose eviction set contains `t` together with `D`,
the replacement pays at least `fee(t) + Σ_{d∈D} fee(d) + GetFee(vsize(R.new))`.  Thus attaching
descendants of total fee `F = totalFee D` raises the lower bound on the cost of replacing `t` by
exactly `F`. -/
theorem BitcoinReplacement.pinning_cost (rate : BitcoinReplacement.FeeRate)
    (t : BitcoinReplacement.Tx) (D : Multiset BitcoinReplacement.Tx)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (hD : t ::ₘ D ≤ R.evicted) :
    t.fee + BitcoinReplacement.totalFee D + rate.getFee R.new.vsize ≤ R.new.fee := by
  have h1 := totalFee_le_of_le hD
  rw [totalFee_cons] at h1
  have := hR.2.1
  have := hR.2.2
  omega

/-- **Pinning cost is exact for rule 4.**  When the eviction set is precisely `t` plus its
descendants `D`, `PaysForRBF` holds iff the replacement pays at least
`fee(t) + Σ_{d∈D} fee(d) + GetFee(vsize)`; so the pinning bound of `pinning_cost` is attained. -/
theorem BitcoinReplacement.pinning_cost_tight (rate : BitcoinReplacement.FeeRate)
    (t : BitcoinReplacement.Tx) (D : Multiset BitcoinReplacement.Tx)
    (R : BitcoinReplacement.Replacement) (hE : R.evicted = t ::ₘ D) :
    BitcoinReplacement.PaysForRBF rate R ↔
      t.fee + BitcoinReplacement.totalFee D + rate.getFee R.new.vsize ≤ R.new.fee := by
  rw [BitcoinReplacement.paysForRBF_iff, hE, totalFee_cons]

/-- **Rule 3 restated (exact `CFeeRate` comparison).**  Every directly conflicting transaction has
a strictly lower fee rate than the replacement, in the `ByRatio` sense:
`fee(t) · vsize(new) < fee(new) · vsize(t)`. -/
theorem BitcoinReplacement.evicted_feerate_dominated (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (t : BitcoinReplacement.Tx) (ht : t ∈ R.direct) :
    t.fee * R.new.vsize < R.new.fee * t.vsize :=
  hR.1 t ht

/-- The `ByRatio` comparison is the ordinary comparison of the exact fractions `fee / vsize`. -/
theorem BitcoinReplacement.feeRateQ_lt_iff (a b : BitcoinReplacement.Tx) :
    a.feeRateQ < b.feeRateQ ↔ BitcoinReplacement.FeeRate.lt a.feeRate b.feeRate :=
  feeRateQ_lt_iff' a b

/-- **Corollary of rule 3.**  Whenever there is at least one direct conflict, the replacement's fee
rate strictly exceeds the minimum fee rate among the directly conflicting (original) transactions:
there is a direct conflict of minimal fee rate, and it is dominated. -/
theorem BitcoinReplacement.min_direct_feerate_lt (rate : BitcoinReplacement.FeeRate)
    (R : BitcoinReplacement.Replacement) (hR : BitcoinReplacement.Valid rate R)
    (hne : R.direct ≠ 0) :
    ∃ t ∈ R.direct, (∀ s ∈ R.direct, t.feeRateQ ≤ s.feeRateQ) ∧
      t.feeRateQ < R.new.feeRateQ := by
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image R.direct.toFinset Tx.feeRateQ
    ⟨x, Multiset.mem_toFinset.2 hx⟩
  rw [Multiset.mem_toFinset] at ht
  refine ⟨t, ht, fun s hs => hmin s (Multiset.mem_toFinset.2 hs), ?_⟩
  rw [feeRateQ_lt_iff']
  exact hR.1 t ht

