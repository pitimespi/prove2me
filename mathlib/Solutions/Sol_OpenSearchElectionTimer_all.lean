import Definitions.Def_OpenSearchElectionTimer

open OpenSearchPreVote OpenSearchElectionTimer

/-! # Randomized election timers -/

/-- Every random delay lies between one millisecond and the bound. -/
theorem OpenSearchElectionTimer.randomDelay_range (M : Nat) (hM : 1 ≤ M) (x : Fin (2 ^ 64)) :
    1 ≤ randomDelay M x ∧ randomDelay M x ≤ M := by
  sorry

/-- **The exact distribution of a delay.** For a bound `1 ≤ M ≤ 2^63` and `1 ≤ d ≤ M`, exactly
`2 · (⌊(2^63 - d) / M⌋ + 1)` of the `2^64` values of `random.nextLong()` give the delay `d`. -/
theorem OpenSearchElectionTimer.randomDelay_card (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card = 2 * ((2 ^ 63 - d) / M + 1) := by
  sorry

/-- **Delays are uniform up to a relative error of `M / 2^63`.** Each delay `d ∈ [1, M]` has between
`2 ⌊2^63 / M⌋` and `2 ⌈2^63 / M⌉` preimages among the `2^64` longs. -/
theorem OpenSearchElectionTimer.randomDelay_near_uniform (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    2 * (2 ^ 63 / M) ≤ (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card ∧
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card ≤ 2 * ((2 ^ 63 + M - 1) / M) := by
  sorry

/-- **Two timers rarely fire close together.** Whatever their offsets, for bounds between `Mmin ≥ 1` and `2^63`, the
probability that two candidates fire less than `δ ≥ 1` apart is at most `(2δ - 1) · ⌈2^63 / Mmin⌉ / 2^63`. -/
theorem OpenSearchElectionTimer.close_pair_prob (a b : Int) (Ma Mb Mmin δ : Nat) (hM : 1 ≤ Mmin)
    (hMa : Mmin ≤ Ma ∧ Ma ≤ 2 ^ 63) (hMb : Mmin ≤ Mb ∧ Mb ≤ 2 ^ 63) (hδ : 1 ≤ δ) :
    ((Finset.univ.filter (fun p : Fin (2 ^ 64) × Fin (2 ^ 64) =>
        |(a + randomDelay Ma p.1) - (b + randomDelay Mb p.2)| < δ)).card : ℚ) / (2 ^ 64) ^ 2 ≤
      (2 * δ - 1 : ℕ) * ((2 ^ 63 + Mmin - 1) / Mmin : ℕ) / 2 ^ 63 := by
  sorry

/-- **A round of competing timers is uncontested with high probability.** For `n ≥ 1` candidates with arbitrary
offsets and with bounds between `Mmin ≥ 1` and `2^63`, the probability that no candidate fires at least `δ ≥ 1` before
all others is at most `contestedBound n δ Mmin = C(n,2) · (2δ - 1) · ⌈2^63 / Mmin⌉ / 2^63`. -/
theorem OpenSearchElectionTimer.contested_prob_le (n δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin n → Int) (bound : Fin n → Nat) (hbound : ∀ i, Mmin ≤ bound i ∧ bound i ≤ 2 ^ 63) :
    ((Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card : ℚ) / (2 ^ 64) ^ n ≤
      contestedBound n δ Mmin := by
  sorry

/-- **Repeated contests become exponentially unlikely, even against an adaptive scheduler.** Over `K` rounds, let the
offsets and bounds of round `k` be chosen as any function of the draws of the earlier rounds (an adversary scheduling
the network may react to what happened so far, but not foresee future draws), with every bound between `Mmin ≥ 1` and
`2^63`. The probability that all `K` rounds are contested with margin `δ ≥ 1` is at most `contestedBound n δ Mmin ^ K`. -/
theorem OpenSearchElectionTimer.all_contested_prob_le (n K δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Int)
    (bound : Fin K → (Fin K → Fin n → Fin (2 ^ 64)) → Fin n → Nat)
    (hbound : ∀ k X i, Mmin ≤ bound k X i ∧ bound k X i ≤ 2 ^ 63)
    (hcausal : ∀ k X X', (∀ m : Fin K, m < k → X m = X' m) → offset k X = offset k X' ∧ bound k X = bound k X') :
    ((Finset.univ.filter (fun X : Fin K → Fin n → Fin (2 ^ 64) =>
        ∀ k, ¬ Uncontested (offset k X) (bound k X) δ (X k))).card : ℚ) / (2 ^ 64) ^ (n * K) ≤
      contestedBound n δ Mmin ^ K := by
  sorry

/-- With OpenSearch's default `cluster.election.max_timeout` of 10 seconds, three competing candidates and a margin of
100 ms (ample for a pre-voting round and an election on a local network), a round is contested with probability below
6%, and five consecutive rounds with probability below one in a million. -/
theorem OpenSearchElectionTimer.default_example :
    contestedBound 3 100 10000 < 6 / 100 ∧ contestedBound 3 100 10000 ^ 5 < 1 / 1000000 := by
  sorry
