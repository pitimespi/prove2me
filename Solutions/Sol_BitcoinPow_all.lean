import Definitions.Def_BitcoinPow

open BitcoinPow

/-! ### Basic facts about the compact fields -/

private theorem compactSize_lt (c : BitVec 32) : compactSize c < 256 := by
  unfold compactSize
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := c.isLt
  omega

private theorem compactWord_lt (c : BitVec 32) : compactWord c < 2 ^ 23 := by
  unfold compactWord
  rw [BitVec.toNat_and]
  have h : (0x007fffff : BitVec 32).toNat = 2 ^ 23 - 1 := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

private theorem pow256_eq (k : Nat) : (256 : Nat) ^ k = 2 ^ (8 * k) := by
  rw [Nat.pow_mul]

/-! ### Theorem 1: overflow flag ⟺ exact value ≥ 2^256 -/

theorem BitcoinPow.overflow_iff (c : BitVec 32) :
    BitcoinPow.compactOverflow c = true ↔ BitcoinPow.width ≤ BitcoinPow.specTarget c := by
  unfold compactOverflow specTarget width
  have hS := compactSize_lt c
  have hW := compactWord_lt c
  generalize compactSize c = S at *
  generalize compactWord c = W at *
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases h3 : S ≤ 3
  · rw [if_pos h3]
    have hle : W / 256 ^ (3 - S) ≤ W := Nat.div_le_self _ _
    have h23 : (2 : Nat) ^ 23 < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) (by decide)
    constructor
    · intro h
      obtain ⟨-, (h | h) | h⟩ := h
      · omega
      · omega
      · omega
    · intro h; omega
  · rw [if_neg h3]
    rcases Nat.lt_or_ge S 33 with h32 | h33
    · -- S ≤ 32: no overflow either way
      have hpow : 256 ^ (S - 3) ≤ 256 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
      have hprod : W * 256 ^ (S - 3) ≤ 2 ^ 23 * 256 ^ 29 :=
        Nat.mul_le_mul (Nat.le_of_lt hW) hpow
      have hlt : 2 ^ 23 * 256 ^ 29 < 2 ^ 256 := by
        rw [pow256_eq, ← Nat.pow_add]
        exact Nat.pow_lt_pow_right (by decide) (by decide)
      constructor
      · intro h
        obtain ⟨-, (h | h) | h⟩ := h
        · omega
        · omega
        · omega
      · intro h; omega
    · rcases Nat.lt_or_ge S 35 with h34 | h35
      · rcases Nat.lt_or_ge S 34 with h33' | h34'
        · -- S = 33
          have hS33 : S = 33 := by omega
          subst hS33
          have h240 : (256 : Nat) ^ (33 - 3) = 2 ^ 240 := by rw [pow256_eq]
          rw [h240]
          have hsplit : (2 : Nat) ^ 256 = 2 ^ 16 * 2 ^ 240 := by rw [← Nat.pow_add]
          constructor
          · intro h
            obtain ⟨hW0, (h | h) | h⟩ := h
            · omega
            · omega
            · rw [hsplit]
              exact Nat.mul_le_mul_right _ (by omega)
          · intro h
            refine ⟨?_, Or.inr ⟨?_, by decide⟩⟩
            · intro hW0; subst hW0; simp at h
            · rcases Nat.lt_or_ge 0xffff W with hgt | hle
              · exact hgt
              · exfalso
                have h1 : W * 2 ^ 240 ≤ 0xffff * 2 ^ 240 := Nat.mul_le_mul_right _ hle
                have h2 : 0xffff * 2 ^ 240 < 2 ^ 16 * 2 ^ 240 := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.two_pow_pos _)
                omega
        · -- S = 34
          have hS34 : S = 34 := by omega
          subst hS34
          have h248 : (256 : Nat) ^ (34 - 3) = 2 ^ 248 := by rw [pow256_eq]
          rw [h248]
          have hsplit : (2 : Nat) ^ 256 = 2 ^ 8 * 2 ^ 248 := by rw [← Nat.pow_add]
          constructor
          · intro h
            obtain ⟨hW0, (h | h) | h⟩ := h
            · omega
            · rw [hsplit]; exact Nat.mul_le_mul_right _ (by omega)
            · rw [hsplit]; exact Nat.mul_le_mul_right _ (by omega)
          · intro h
            refine ⟨?_, Or.inl (Or.inr ⟨?_, by decide⟩)⟩
            · intro hW0; subst hW0; simp at h
            · rcases Nat.lt_or_ge 0xff W with hgt | hle
              · exact hgt
              · exfalso
                have h1 : W * 2 ^ 248 ≤ 0xff * 2 ^ 248 := Nat.mul_le_mul_right _ hle
                have h2 : 0xff * 2 ^ 248 < 2 ^ 8 * 2 ^ 248 := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.two_pow_pos _)
                omega
      · -- S ≥ 35
        have hpow : 2 ^ 256 ≤ 256 ^ (S - 3) := by
          rw [pow256_eq]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        constructor
        · intro h
          obtain ⟨hW0, -⟩ := h
          calc 2 ^ 256 ≤ 256 ^ (S - 3) := hpow
            _ = 1 * 256 ^ (S - 3) := (Nat.one_mul _).symm
            _ ≤ W * 256 ^ (S - 3) := Nat.mul_le_mul_right _ (by omega)
        · intro h
          refine ⟨?_, Or.inl (Or.inl (by omega))⟩
          intro hW0; subst hW0; simp at h

/-! ### Theorem 2: without overflow, SetCompact is the exact value -/

theorem BitcoinPow.setCompact_eq_spec (c : BitVec 32) (h : BitcoinPow.compactOverflow c = false) :
    BitcoinPow.setCompact c = BitcoinPow.specTarget c := by
  have hlt : specTarget c < width := by
    rcases Nat.lt_or_ge (specTarget c) width with hlt | hge
    · exact hlt
    · have := (BitcoinPow.overflow_iff c).2 hge; rw [h] at this; exact absurd this (by decide)
  unfold setCompact specTarget at *
  simp only [] at hlt ⊢
  by_cases h3 : compactSize c ≤ 3
  · simp only [if_pos h3, Nat.shiftRight_eq_div_pow, ← pow256_eq]
  · simp only [if_neg h3] at hlt ⊢
    rw [Nat.shiftLeft_eq, ← pow256_eq]
    exact Nat.mod_eq_of_lt hlt

/-! ### Theorem 6: proof-of-work acceptance -/

theorem BitcoinPow.checkProofOfWork_iff (hash : Nat) (nBits : BitVec 32) :
    BitcoinPow.checkProofOfWork hash nBits = true ↔
      BitcoinPow.compactNegative nBits = false ∧ BitcoinPow.compactOverflow nBits = false ∧
      0 < BitcoinPow.specTarget nBits ∧ BitcoinPow.specTarget nBits ≤ BitcoinPow.powLimit ∧
      hash ≤ BitcoinPow.specTarget nBits := by
  unfold checkProofOfWork deriveTarget
  simp only []
  by_cases hc : (compactNegative nBits || decide (setCompact nBits = 0) || compactOverflow nBits ||
      decide (powLimit < setCompact nBits)) = true
  · rw [if_pos hc]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨hneg, hov, hpos, hlim, -⟩
    have hs := BitcoinPow.setCompact_eq_spec nBits hov
    rw [hneg, hov, hs] at hc
    simp only [Bool.false_eq_true, false_or, or_false] at hc
    omega
  · rw [if_neg hc]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
    obtain ⟨⟨⟨hneg, hzero⟩, hov⟩, hlim⟩ := hc
    have hneg' : compactNegative nBits = false := by
      cases h : compactNegative nBits
      · rfl
      · exact absurd h hneg
    have hov' : compactOverflow nBits = false := by
      cases h : compactOverflow nBits
      · rfl
      · exact absurd h hov
    have hs := BitcoinPow.setCompact_eq_spec nBits hov'
    rw [hs] at hzero hlim ⊢
    simp only [decide_eq_true_eq]
    constructor
    · intro h; exact ⟨hneg', hov', by omega, by omega, h⟩
    · rintro ⟨-, -, -, -, h⟩; exact h

/-! ### Theorem 7: the timespan clamp -/

theorem BitcoinPow.clamp_bounds (actual : Int) :
    ((BitcoinPow.targetTimespan / 4 : Nat) : Int) ≤ BitcoinPow.clampTimespan actual ∧
    BitcoinPow.clampTimespan actual ≤ ((BitcoinPow.targetTimespan * 4 : Nat) : Int) := by
  unfold clampTimespan targetTimespan
  simp only []
  by_cases h1 : actual < ((14 * 24 * 60 * 60 / 4 : Nat) : Int)
  · rw [if_pos h1]; constructor <;> omega
  · rw [if_neg h1]
    by_cases h2 : ((14 * 24 * 60 * 60 * 4 : Nat) : Int) < actual
    · rw [if_pos h2]; constructor <;> omega
    · rw [if_neg h2]; constructor <;> omega

/-! ### Theorem 9: no retarget off the interval boundary -/

theorem BitcoinPow.nextWork_off_boundary (lastHeight : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (h : (lastHeight + 1) % BitcoinPow.difficultyAdjustmentInterval ≠ 0) :
    BitcoinPow.nextWorkRequired lastHeight lastBits lastTime firstTime = lastBits ∧
    BitcoinPow.permittedTransition (lastHeight + 1) lastBits lastBits = true := by
  constructor
  · unfold nextWorkRequired; rw [if_pos h]
  · unfold permittedTransition; rw [if_neg h]; simp

/-! ### The GetCompact rounding analysis -/

/-- Conjunction with a single power of two isolates that bit. -/
private theorem and_two_pow_eq (n k : Nat) : n &&& 2 ^ k = ((n / 2 ^ k) % 2) * 2 ^ k := by
  have h1 : (n &&& 2 ^ k) / 2 ^ k = (n / 2 ^ k) % 2 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos k), Nat.and_one_is_mod]
  have h2 : (n &&& 2 ^ k) % 2 ^ k = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  have h := Nat.div_add_mod (n &&& 2 ^ k) (2 ^ k)
  rw [h1, h2, Nat.add_zero, Nat.mul_comm] at h
  exact h.symm

/-- Fields of a compact word assembled as `mantissa ||| size <<< 24` with a 23-bit mantissa. -/
private theorem fields_of_assembled (a n : Nat) (ha : a < 2 ^ 23) (hn : n < 256) :
    compactSize (BitVec.ofNat 32 (a ||| n <<< 24)) = n ∧
    compactWord (BitVec.ofNat 32 (a ||| n <<< 24)) = a ∧
    compactNegative (BitVec.ofNat 32 (a ||| n <<< 24)) = false := by
  have hx : a ||| n <<< 24 < 2 ^ 32 := by
    apply Nat.or_lt_two_pow
    · exact Nat.lt_trans ha (by decide)
    · rw [Nat.shiftLeft_eq]
      calc n * 2 ^ 24 < 256 * 2 ^ 24 := Nat.mul_lt_mul_of_pos_right hn (by decide)
        _ = 2 ^ 32 := by decide
  have htoNat : (BitVec.ofNat 32 (a ||| n <<< 24)).toNat = a ||| n <<< 24 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hx
  have hdiv24 : (a ||| n <<< 24) / 2 ^ 24 = n := by
    rw [Nat.or_div_two_pow, Nat.div_eq_of_lt (Nat.lt_trans ha (by decide)), Nat.zero_or,
      ← Nat.shiftRight_eq_div_pow, Nat.shiftLeft_shiftRight]
  have hmod23 : (a ||| n <<< 24) % 2 ^ 23 = a := by
    rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt ha, Nat.shiftLeft_eq]
    have : n * 2 ^ 24 = (n * 2) * 2 ^ 23 := by rw [Nat.mul_assoc]
    rw [this, Nat.mul_mod_left, Nat.or_zero]
  have hdiv23 : (a ||| n <<< 24) / 2 ^ 23 = n * 2 := by
    rw [Nat.or_div_two_pow, Nat.div_eq_of_lt ha, Nat.zero_or, Nat.shiftLeft_eq]
    have : n * 2 ^ 24 = (n * 2) * 2 ^ 23 := by rw [Nat.mul_assoc]
    rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos 23)]
  refine ⟨?_, ?_, ?_⟩
  · unfold compactSize
    rw [BitVec.toNat_ushiftRight, htoNat, Nat.shiftRight_eq_div_pow, hdiv24]
  · unfold compactWord
    rw [BitVec.toNat_and, htoNat]
    have h : (0x007fffff : BitVec 32).toNat = 2 ^ 23 - 1 := rfl
    rw [h, Nat.and_two_pow_sub_one_eq_mod, hmod23]
  · unfold compactNegative
    have hbit : ((BitVec.ofNat 32 (a ||| n <<< 24)) &&& 0x00800000) = 0 := by
      rw [BitVec.toNat_eq, BitVec.toNat_and, htoNat]
      have h : (0x00800000 : BitVec 32).toNat = 2 ^ 23 := rfl
      have h0 : (0 : BitVec 32).toNat = 0 := rfl
      rw [h, h0, and_two_pow_eq, hdiv23]
      simp [Nat.mul_mod_left]
    rw [hbit]
    simp

/-- The mantissa bit test is a comparison against `2 ^ 23` for 24-bit values. -/
private theorem adjust_iff (m : Nat) (hm : m < 2 ^ 24) :
    (m &&& 0x00800000 != 0) = true ↔ 2 ^ 23 ≤ m := by
  have h : (0x00800000 : Nat) = 2 ^ 23 := by decide
  rw [bne_iff_ne, ne_eq, h, and_two_pow_eq]
  constructor
  · intro hne
    rcases Nat.lt_or_ge m (2 ^ 23) with hlt | hge
    · exfalso; apply hne; rw [Nat.div_eq_of_lt hlt]
    · exact hge
  · intro hge
    have h1 : m / 2 ^ 23 = 1 := by
      have := Nat.div_le_div_right (c := 2 ^ 23) (Nat.le_of_lt hm)
      have h2 : 2 ^ 24 / 2 ^ 23 = 2 := by decide
      have h3 : 1 ≤ m / 2 ^ 23 := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by simpa using hge)
      omega
    rw [h1]; decide

private theorem bitLength_eq (v : Nat) (hv : v ≠ 0) : bitLength v = Nat.log2 v + 1 := by
  unfold bitLength; rw [if_neg hv]

/-- Number of low bits that `GetCompact` discards, as a function of the index of the top bit. -/
private def dropBits (L : Nat) : Nat :=
  if L < 16 then 0 else 8 * (L / 8) - 16 + (if L % 8 = 7 then 8 else 0)

private theorem dropBits_le (L : Nat) : dropBits L ≤ L := by
  unfold dropBits
  split
  · exact Nat.zero_le _
  · split <;> omega

/-- The core identity: `SetCompact ∘ GetCompact` clears the low `dropBits (log2 v)` bits of `v`. -/
private theorem round_eq (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256) :
    setCompact (getCompact v) =
      (v / 2 ^ dropBits (Nat.log2 v)) * 2 ^ dropBits (Nat.log2 v) := by
  have hL := Nat.log2_self_le hv0
  have hL' := @Nat.lt_log2_self v
  have hL256 : Nat.log2 v < 256 := (Nat.log2_lt hv0).2 hv
  generalize hLdef : Nat.log2 v = L at *
  have hmod8 : L % 8 < 8 := Nat.mod_lt _ (by decide)
  unfold getCompact
  rw [bitLength_eq v hv0, hLdef]
  have hsize : (L + 1 + 7) / 8 = L / 8 + 1 := by omega
  rw [hsize]
  simp only []
  rcases Nat.lt_or_ge L 24 with hsmall | hbig
  · -- nSize ≤ 3: mantissa = v * 2 ^ k, k = 8 * (2 - L / 8)
    have h3 : L / 8 + 1 ≤ 3 := by omega
    rw [if_pos h3]
    have hv64 : v % 2 ^ 64 = v :=
      Nat.mod_eq_of_lt (Nat.lt_trans hL' (Nat.pow_lt_pow_right (by decide) (by omega)))
    rw [hv64, Nat.shiftLeft_eq]
    have hk : 8 * (3 - (L / 8 + 1)) = 8 * (2 - L / 8) := by omega
    rw [hk]
    generalize hkdef : 8 * (2 - L / 8) = k
    have hmant_lo : 2 ^ (L % 8 + 16) ≤ v * 2 ^ k := by
      have : L % 8 + 16 = L + k := by omega
      rw [this, Nat.pow_add]; exact Nat.mul_le_mul_right _ hL
    have hmant_hi : v * 2 ^ k < 2 ^ (L % 8 + 17) := by
      have : L % 8 + 17 = (L + 1) + k := by omega
      rw [this, Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hL' (Nat.two_pow_pos _)
    have hmant24 : v * 2 ^ k < 2 ^ 24 :=
      Nat.lt_of_lt_of_le hmant_hi (Nat.pow_le_pow_right (by decide) (by omega))
    have hmant32 : v * 2 ^ k % 2 ^ 32 = v * 2 ^ k :=
      Nat.mod_eq_of_lt (Nat.lt_trans hmant24 (by decide))
    rw [hmant32]
    by_cases hadj : (v * 2 ^ k &&& 0x00800000 != 0) = true
    · -- adjust: L % 8 = 7, so L ∈ {7, 15, 23}
      have h23 : 2 ^ 23 ≤ v * 2 ^ k := (adjust_iff _ hmant24).1 hadj
      have hL7 : L % 8 = 7 := by
        rcases Nat.lt_or_ge (L % 8) 7 with hlt | hge
        · exfalso
          have hlt23 : L % 8 + 17 ≤ 23 := by omega
          have : v * 2 ^ k < 2 ^ 23 :=
            Nat.lt_of_lt_of_le hmant_hi (Nat.pow_le_pow_right (by decide) hlt23)
          omega
        · omega
      simp only [if_pos hadj]
      by_cases h16 : L < 16
      · -- L ∈ {7, 15}: the adjusted word still has nSize' ≤ 3, result exact
        have hk8 : 8 ≤ k := by omega
        have hm' : (v * 2 ^ k) >>> 8 = v * 2 ^ (k - 8) := by
          rw [Nat.shiftRight_eq_div_pow]
          have : 2 ^ k = 2 ^ (k - 8) * 2 ^ 8 := by rw [← Nat.pow_add]; congr 1; omega
          rw [this, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos 8)]
        rw [hm']
        have ha : v * 2 ^ (k - 8) < 2 ^ 23 := by
          have hsplit : v * 2 ^ k = v * 2 ^ (k - 8) * 2 ^ 8 := by
            rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
          rw [hsplit] at hmant24
          have h24 : (2 : Nat) ^ 24 = 2 ^ 16 * 2 ^ 8 := by rw [← Nat.pow_add]
          rw [h24] at hmant24
          exact Nat.lt_of_lt_of_le (Nat.lt_of_mul_lt_mul_right hmant24)
            (Nat.pow_le_pow_right (by decide) (by decide))
        obtain ⟨hs, hw, -⟩ := fields_of_assembled (v * 2 ^ (k - 8)) (L / 8 + 1 + 1) ha (by omega)
        simp only [setCompact, hs, hw]
        have h3' : L / 8 + 1 + 1 ≤ 3 := by omega
        rw [if_pos h3', Nat.shiftRight_eq_div_pow]
        have hdrop : dropBits L = 0 := by unfold dropBits; rw [if_pos h16]
        rw [hdrop]
        simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one]
        have : 8 * (3 - (L / 8 + 1 + 1)) = k - 8 := by omega
        rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      · -- L = 23: k = 0, the adjusted word has nSize' = 4
        have hk0 : k = 0 := by omega
        have hm' : (v * 2 ^ k) >>> 8 = v / 2 ^ 8 := by
          rw [hk0, Nat.pow_zero, Nat.mul_one, Nat.shiftRight_eq_div_pow]
        rw [hm']
        have ha : v / 2 ^ 8 < 2 ^ 23 := by
          apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
          rw [hk0, Nat.pow_zero, Nat.mul_one] at hmant24
          exact Nat.lt_of_lt_of_le hmant24 (by decide)
        obtain ⟨hs, hw, -⟩ := fields_of_assembled (v / 2 ^ 8) (L / 8 + 1 + 1) ha (by omega)
        simp only [setCompact, hs, hw]
        have h3' : ¬ (L / 8 + 1 + 1 ≤ 3) := by omega
        rw [if_neg h3', Nat.shiftLeft_eq]
        have hexp : 8 * (L / 8 + 1 + 1 - 3) = 8 := by omega
        rw [hexp]
        have hdrop : dropBits L = 8 := by
          unfold dropBits; rw [if_neg h16, if_pos hL7]; omega
        rw [hdrop]
        apply Nat.mod_eq_of_lt
        exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hv
    · -- no adjust: result exact
      simp only [if_neg hadj]
      have ha : v * 2 ^ k < 2 ^ 23 := by
        rcases Nat.lt_or_ge (v * 2 ^ k) (2 ^ 23) with hlt | hge
        · exact hlt
        · exact absurd ((adjust_iff _ hmant24).2 hge) hadj
      obtain ⟨hs, hw, -⟩ := fields_of_assembled (v * 2 ^ k) (L / 8 + 1) ha (by omega)
      simp only [setCompact, hs, hw]
      rw [if_pos h3, Nat.shiftRight_eq_div_pow]
      have hL7 : L % 8 ≠ 7 := by
        intro h7
        apply hadj
        apply (adjust_iff _ hmant24).2
        calc 2 ^ 23 = 2 ^ (L % 8 + 16) := by rw [h7]
          _ ≤ v * 2 ^ k := hmant_lo
      have hdrop : dropBits L = 0 := by
        unfold dropBits
        by_cases h16 : L < 16
        · rw [if_pos h16]
        · rw [if_neg h16, if_neg hL7]; omega
      rw [hdrop]
      simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one]
      have : 8 * (3 - (L / 8 + 1)) = k := by omega
      rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · -- nSize > 3: mantissa = v / 2 ^ s with s = 8 * (L / 8) - 16
    have h3 : ¬ (L / 8 + 1 ≤ 3) := by omega
    rw [if_neg h3, Nat.shiftRight_eq_div_pow]
    have hs : 8 * (L / 8 + 1 - 3) = 8 * (L / 8) - 16 := by omega
    rw [hs]
    generalize hsdef : 8 * (L / 8) - 16 = s
    have hmant_lo : 2 ^ (L % 8 + 16) ≤ v / 2 ^ s := by
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
      rw [← Nat.pow_add]
      have : L % 8 + 16 + s = L := by omega
      rw [this]; exact hL
    have hmant_hi : v / 2 ^ s < 2 ^ (L % 8 + 17) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      rw [← Nat.pow_add]
      have : L % 8 + 17 + s = L + 1 := by omega
      rw [this]; exact hL'
    have hmant24 : v / 2 ^ s < 2 ^ 24 :=
      Nat.lt_of_lt_of_le hmant_hi (Nat.pow_le_pow_right (by decide) (by omega))
    have hmant64 : v / 2 ^ s % 2 ^ 64 = v / 2 ^ s :=
      Nat.mod_eq_of_lt (Nat.lt_trans hmant24 (by decide))
    have hmant32 : v / 2 ^ s % 2 ^ 32 = v / 2 ^ s :=
      Nat.mod_eq_of_lt (Nat.lt_trans hmant24 (by decide))
    rw [hmant64, hmant32]
    have hdrop_lt : ¬ (L < 16) := by omega
    by_cases hadj : (v / 2 ^ s &&& 0x00800000 != 0) = true
    · have h23 : 2 ^ 23 ≤ v / 2 ^ s := (adjust_iff _ hmant24).1 hadj
      have hL7 : L % 8 = 7 := by
        rcases Nat.lt_or_ge (L % 8) 7 with hlt | hge
        · exfalso
          have hlt23 : L % 8 + 17 ≤ 23 := by omega
          have : v / 2 ^ s < 2 ^ 23 :=
            Nat.lt_of_lt_of_le hmant_hi (Nat.pow_le_pow_right (by decide) hlt23)
          omega
        · omega
      simp only [if_pos hadj]
      have hm' : (v / 2 ^ s) >>> 8 = v / 2 ^ (s + 8) := by
        rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
      rw [hm']
      have ha : v / 2 ^ (s + 8) < 2 ^ 23 := by
        rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
        exact Nat.lt_of_lt_of_le hmant24 (by decide)
      obtain ⟨hsz, hw, -⟩ := fields_of_assembled (v / 2 ^ (s + 8)) (L / 8 + 1 + 1) ha (by omega)
      simp only [setCompact, hsz, hw]
      have h3' : ¬ (L / 8 + 1 + 1 ≤ 3) := by omega
      rw [if_neg h3', Nat.shiftLeft_eq]
      have hexp : 8 * (L / 8 + 1 + 1 - 3) = s + 8 := by omega
      rw [hexp]
      have hdrop : dropBits L = s + 8 := by
        unfold dropBits; rw [if_neg hdrop_lt, if_pos hL7]; omega
      rw [hdrop]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hv
    · simp only [if_neg hadj]
      have ha : v / 2 ^ s < 2 ^ 23 := by
        rcases Nat.lt_or_ge (v / 2 ^ s) (2 ^ 23) with hlt | hge
        · exact hlt
        · exact absurd ((adjust_iff _ hmant24).2 hge) hadj
      obtain ⟨hsz, hw, -⟩ := fields_of_assembled (v / 2 ^ s) (L / 8 + 1) ha (by omega)
      simp only [setCompact, hsz, hw]
      rw [if_neg h3, Nat.shiftLeft_eq]
      have hexp : 8 * (L / 8 + 1 - 3) = s := by omega
      rw [hexp]
      have hL7 : L % 8 ≠ 7 := by
        intro h7
        apply hadj
        apply (adjust_iff _ hmant24).2
        calc 2 ^ 23 = 2 ^ (L % 8 + 16) := by rw [h7]
          _ ≤ v / 2 ^ s := hmant_lo
      have hdrop : dropBits L = s := by
        unfold dropBits; rw [if_neg hdrop_lt, if_neg hL7]; omega
      rw [hdrop]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hv

/-! ### Consequences of the rounding identity -/

private theorem round_zero : setCompact (getCompact 0) = 0 := by decide

private theorem powLimit_lt_width : powLimit < width := by
  unfold powLimit width
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide) (by decide))

theorem BitcoinPow.getCompact_le (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ v := by
  by_cases hv0 : v = 0
  · subst hv0; rw [round_zero]; exact Nat.le_refl 0
  · rw [round_eq v hv0 hv]; exact Nat.div_mul_le_self _ _

/-- The rounded value keeps the top bit of `v`. -/
private theorem round_ge_top (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256) :
    2 ^ Nat.log2 v ≤ setCompact (getCompact v) := by
  rw [round_eq v hv0 hv]
  have he := dropBits_le (Nat.log2 v)
  have hL := Nat.log2_self_le hv0
  generalize Nat.log2 v = L at *
  generalize dropBits L = e at *
  have hsplit : 2 ^ L = 2 ^ (L - e) * 2 ^ e := by rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit]
  apply Nat.mul_le_mul_right
  apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
  rw [← hsplit]; exact hL

theorem BitcoinPow.round_mono (v w : Nat) (hvw : v ≤ w) (hw : w < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ BitcoinPow.setCompact (BitcoinPow.getCompact w) := by
  by_cases hv0 : v = 0
  · subst hv0; rw [round_zero]; exact Nat.zero_le _
  have hw0 : w ≠ 0 := by omega
  have hv : v < width := Nat.lt_of_le_of_lt hvw hw
  have hLle : Nat.log2 v ≤ Nat.log2 w :=
    (Nat.le_log2 hw0).2 (Nat.le_trans (Nat.log2_self_le hv0) hvw)
  rcases Nat.lt_or_ge (Nat.log2 v) (Nat.log2 w) with hlt | hge
  · -- strictly fewer bits: everything below the top bit of w
    apply Nat.le_of_lt
    calc setCompact (getCompact v) ≤ v := BitcoinPow.getCompact_le v hv
      _ < 2 ^ (Nat.log2 v + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ Nat.log2 w := Nat.pow_le_pow_right (by decide) hlt
      _ ≤ setCompact (getCompact w) := round_ge_top w hw0 hw
  · have heq : Nat.log2 v = Nat.log2 w := Nat.le_antisymm hLle hge
    rw [round_eq v hv0 hv, round_eq w hw0 hw, heq]
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right hvw)

/-- Any word assembled by GetCompact's final step from a 24-bit mantissa and a size at most 32
decodes as non-negative and non-overflowing. -/
private theorem assembled_valid (M n0 : Nat) (hM : M < 2 ^ 24) (hn : n0 ≤ 32) :
    compactNegative (BitVec.ofNat 32
      ((if (M &&& 0x00800000 != 0) = true then M >>> 8 else M) |||
        (if (M &&& 0x00800000 != 0) = true then n0 + 1 else n0) <<< 24)) = false ∧
    compactOverflow (BitVec.ofNat 32
      ((if (M &&& 0x00800000 != 0) = true then M >>> 8 else M) |||
        (if (M &&& 0x00800000 != 0) = true then n0 + 1 else n0) <<< 24)) = false := by
  by_cases hadj : (M &&& 0x00800000 != 0) = true
  · simp only [if_pos hadj]
    have hm : M >>> 8 < 2 ^ 16 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      exact Nat.lt_of_lt_of_le hM (by decide)
    have hm23 : M >>> 8 < 2 ^ 23 := Nat.lt_of_lt_of_le hm (by decide)
    obtain ⟨hs, hw, hneg⟩ := fields_of_assembled (M >>> 8) (n0 + 1) hm23 (by omega)
    refine ⟨hneg, ?_⟩
    unfold compactOverflow
    rw [hs, hw]
    generalize hm' : M >>> 8 = m at *
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_false_imp, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      Nat.not_lt]
    intro _
    refine ⟨⟨by omega, fun _ => by omega⟩, fun h => ?_⟩
    simp only [decide_eq_true_eq] at h
    omega
  · simp only [if_neg hadj]
    have hm23 : M < 2 ^ 23 := by
      rcases Nat.lt_or_ge M (2 ^ 23) with hlt | hge
      · exact hlt
      · exact absurd ((adjust_iff M hM).2 hge) hadj
    obtain ⟨hs, hw, hneg⟩ := fields_of_assembled M n0 hm23 (by omega)
    refine ⟨hneg, ?_⟩
    unfold compactOverflow
    rw [hs, hw]
    simp only [bne_iff_ne, ne_eq, Bool.and_eq_false_imp, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      Nat.not_lt]
    intro _
    exact ⟨⟨by omega, fun _ => by omega⟩, fun _ => by omega⟩

theorem BitcoinPow.getCompact_valid (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.compactNegative (BitcoinPow.getCompact v) = false ∧
    BitcoinPow.compactOverflow (BitcoinPow.getCompact v) = false := by
  by_cases hv0 : v = 0
  · subst hv0; decide
  have hL := Nat.log2_self_le hv0
  have hL' := @Nat.lt_log2_self v
  have hL256 : Nat.log2 v < 256 := (Nat.log2_lt hv0).2 hv
  unfold getCompact
  rw [bitLength_eq v hv0]
  generalize hLdef : Nat.log2 v = L at *
  have hsize : (L + 1 + 7) / 8 = L / 8 + 1 := by omega
  rw [hsize]
  simp only []
  apply assembled_valid
  · -- the pre-adjustment mantissa is below 2^24
    split
    · rename_i h3
      have hv64 : v % 2 ^ 64 = v :=
        Nat.mod_eq_of_lt (Nat.lt_trans hL' (Nat.pow_lt_pow_right (by decide) (by omega)))
      rw [hv64, Nat.shiftLeft_eq]
      have hbound : v * 2 ^ (8 * (3 - (L / 8 + 1))) < 2 ^ 24 := by
        calc v * 2 ^ (8 * (3 - (L / 8 + 1))) < 2 ^ (L + 1) * 2 ^ (8 * (3 - (L / 8 + 1))) :=
              Nat.mul_lt_mul_of_pos_right hL' (Nat.two_pow_pos _)
          _ = 2 ^ ((L + 1) + 8 * (3 - (L / 8 + 1))) := (Nat.pow_add _ _ _).symm
          _ ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hbound
    · rename_i h3
      rw [Nat.shiftRight_eq_div_pow]
      have hbound : v / 2 ^ (8 * (L / 8 + 1 - 3)) < 2 ^ 24 := by
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
        rw [← Nat.pow_add]
        exact Nat.lt_of_lt_of_le hL' (Nat.pow_le_pow_right (by decide) (by omega))
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hbound)
  · omega

/-- The capped value never exceeds the proof-of-work limit. -/
private theorem cap_le (x : Nat) : (if powLimit < x then powLimit else x) ≤ powLimit := by
  split <;> omega

private theorem cap_mono (x y : Nat) (h : x ≤ y) :
    (if powLimit < x then powLimit else x) ≤ (if powLimit < y then powLimit else y) := by
  split <;> split <;> omega

theorem BitcoinPow.nextWork_le_powLimit (lastBits : BitVec 32) (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork lastBits lastTime firstTime) ≤ BitcoinPow.powLimit := by
  unfold calculateNextWork
  simp only []
  have hcap := cap_le ((setCompact lastBits * (clampTimespan (lastTime - firstTime)).toNat % width) / targetTimespan)
  exact Nat.le_trans (BitcoinPow.getCompact_le _ (Nat.lt_of_le_of_lt hcap powLimit_lt_width)) hcap

theorem BitcoinPow.nextWork_permitted (height : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (hh : height % BitcoinPow.difficultyAdjustmentInterval = 0)
    (hold : BitcoinPow.setCompact lastBits ≤ BitcoinPow.powLimit) :
    BitcoinPow.permittedTransition height lastBits
      (BitcoinPow.calculateNextWork lastBits lastTime firstTime) = true := by
  unfold permittedTransition calculateNextWork
  rw [if_pos hh]
  simp only []
  -- name the ingredients
  have hclamp := BitcoinPow.clamp_bounds (lastTime - firstTime)
  generalize hts : (clampTimespan (lastTime - firstTime)).toNat = ts at *
  have hts_lo : targetTimespan / 4 ≤ ts := by omega
  have hts_hi : ts ≤ targetTimespan * 4 := by omega
  generalize hold' : setCompact lastBits = old at *
  -- no 256-bit wrap-around in any of the three products
  have hT : targetTimespan * 4 < 2 ^ 32 := by decide
  have hprod : ∀ t, t ≤ targetTimespan * 4 → old * t < width := by
    intro t ht
    calc old * t ≤ powLimit * (targetTimespan * 4) := Nat.mul_le_mul hold ht
      _ < 2 ^ 224 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_le (by unfold powLimit; omega) (Nat.le_of_lt hT) (Nat.two_pow_pos _)
      _ = width := by unfold width; rw [← Nat.pow_add]
  have hq : targetTimespan / 4 ≤ targetTimespan * 4 := by unfold targetTimespan; omega
  have hp1 := hprod ts hts_hi
  have hp2 := hprod (targetTimespan * 4) (Nat.le_refl _)
  have hp3 := hprod (targetTimespan / 4) hq
  simp only [Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2, Nat.mod_eq_of_lt hp3]
  -- the three capped quotients, ordered
  have h1 : old * (targetTimespan / 4) / targetTimespan ≤ old * ts / targetTimespan :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ hts_lo)
  have h2 : old * ts / targetTimespan ≤ old * (targetTimespan * 4) / targetTimespan :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ hts_hi)
  have hmin := cap_mono _ _ h1
  have hmax := cap_mono _ _ h2
  have hobs_lt : (if powLimit < old * ts / targetTimespan then powLimit else old * ts / targetTimespan) < width :=
    Nat.lt_of_le_of_lt (cap_le _) powLimit_lt_width
  have hmax_lt : (if powLimit < old * (targetTimespan * 4) / targetTimespan then powLimit
      else old * (targetTimespan * 4) / targetTimespan) < width :=
    Nat.lt_of_le_of_lt (cap_le _) powLimit_lt_width
  have hA := BitcoinPow.round_mono _ _ hmax hmax_lt
  have hB := BitcoinPow.round_mono _ _ hmin hobs_lt
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, gt_iff_lt]
  exact ⟨hA, hB⟩
