import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

/-- One iteration of the loop. -/
theorem BitcoinMerkle.rootLoop_step {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = BitcoinMerkle.rootLoop c z (BitcoinMerkle.pairUp c hs) (m || BitcoinMerkle.hasEqualPair hs) := by
  conv => lhs; rw [rootLoop]
  rw [dif_pos h]

/-- Loop exit. -/
theorem BitcoinMerkle.rootLoop_stop {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : ¬ 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = (hs.headD z, m) := by
  rw [rootLoop, dif_neg h]

theorem BitcoinMerkle.root_nil {H : Type} [DecidableEq H] (c : H → H → H) (z : H) :
    BitcoinMerkle.computeMerkleRoot c z [] = (z, false) := by
  unfold computeMerkleRoot
  rw [BitcoinMerkle.rootLoop_stop c z [] false (by simp)]
  rfl

theorem BitcoinMerkle.root_single {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a : H) :
    BitcoinMerkle.computeMerkleRoot c z [a] = (a, false) := by
  unfold computeMerkleRoot
  rw [BitcoinMerkle.rootLoop_stop c z [a] false (by simp)]
  rfl

theorem BitcoinMerkle.root_pair {H : Type} [DecidableEq H] (c : H → H → H) (z : H) (a b : H) :
    BitcoinMerkle.computeMerkleRoot c z [a, b] = (c a b, decide (a = b)) := by
  unfold computeMerkleRoot
  rw [BitcoinMerkle.rootLoop_step c z [a, b] false (by simp)]
  simp only [pairUp, hasEqualPair, Bool.false_or, Bool.or_false]
  rw [BitcoinMerkle.rootLoop_stop c z [c a b] _ (by simp)]
  rfl

/-- The root does not depend on the incoming flag. -/
theorem BitcoinMerkle.rootLoop_fst {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m m' : Bool) : (BitcoinMerkle.rootLoop c z hs m).1 = (BitcoinMerkle.rootLoop c z hs m').1 := by
  by_cases h : 1 < hs.length
  · rw [BitcoinMerkle.rootLoop_step c z hs m h, BitcoinMerkle.rootLoop_step c z hs m' h]
    exact BitcoinMerkle.rootLoop_fst c z (pairUp c hs) _ _
  · rw [BitcoinMerkle.rootLoop_stop c z hs m h, BitcoinMerkle.rootLoop_stop c z hs m' h]
termination_by hs.length
decreasing_by
  simp_wf
  rw [pairUp_length]
  omega

/-- Once set, the flag stays set. -/
theorem BitcoinMerkle.rootLoop_sticky {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) : (BitcoinMerkle.rootLoop c z hs true).2 = true := by
  by_cases h : 1 < hs.length
  · rw [BitcoinMerkle.rootLoop_step c z hs true h]
    simp only [Bool.true_or]
    exact BitcoinMerkle.rootLoop_sticky c z (pairUp c hs)
  · rw [BitcoinMerkle.rootLoop_stop c z hs true h]
termination_by hs.length
decreasing_by
  simp_wf
  rw [pairUp_length]
  omega

theorem BitcoinMerkle.pairUp_append_even {H : Type} [DecidableEq H] (c : H → H → H) :
    ∀ (l r : List H), l.length % 2 = 0 → BitcoinMerkle.pairUp c (l ++ r) = BitcoinMerkle.pairUp c l ++ BitcoinMerkle.pairUp c r
  | [], r, _ => by simp [pairUp]
  | [a], r, h => by simp at h
  | a :: b :: rest, r, h => by
    simp only [List.length_cons] at h
    have h' : rest.length % 2 = 0 := by omega
    simp only [List.cons_append, pairUp, List.cons.injEq, true_and]
    exact BitcoinMerkle.pairUp_append_even c rest r h'

theorem BitcoinMerkle.hasEqualPair_append_even {H : Type} [DecidableEq H] :
    ∀ (l r : List H), l.length % 2 = 0 →
      BitcoinMerkle.hasEqualPair (l ++ r) = (BitcoinMerkle.hasEqualPair l || BitcoinMerkle.hasEqualPair r)
  | [], r, _ => by simp [hasEqualPair]
  | [a], r, h => by simp at h
  | a :: b :: rest, r, h => by
    simp only [List.length_cons] at h
    have h' : rest.length % 2 = 0 := by omega
    simp only [List.cons_append, hasEqualPair, Bool.or_assoc]
    rw [BitcoinMerkle.hasEqualPair_append_even rest r h']

/-- Level-0 form of CVE-2012-2459: duplicating the last leaf of an odd-length list leaves the
root unchanged, and the duplicate is detected. -/
theorem BitcoinMerkle.dup_leaf {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (l : List H) (a : H) (hne : l ≠ []) (heven : l.length % 2 = 0) :
    (BitcoinMerkle.computeMerkleRoot c z (l ++ [a])).1 = (BitcoinMerkle.computeMerkleRoot c z (l ++ [a, a])).1 ∧
    (BitcoinMerkle.computeMerkleRoot c z (l ++ [a, a])).2 = true := by
  have hlen : 0 < l.length := List.length_pos_iff.2 hne
  have hp : pairUp c (l ++ [a]) = pairUp c (l ++ [a, a]) := by
    rw [BitcoinMerkle.pairUp_append_even c l [a] heven, BitcoinMerkle.pairUp_append_even c l [a, a] heven]
    simp [pairUp]
  have hq : hasEqualPair (l ++ [a, a]) = true := by
    rw [BitcoinMerkle.hasEqualPair_append_even l [a, a] heven]
    simp [hasEqualPair]
  have h1 : 1 < (l ++ [a]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have h2 : 1 < (l ++ [a, a]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  unfold computeMerkleRoot
  constructor
  · rw [BitcoinMerkle.rootLoop_step c z _ false h1, BitcoinMerkle.rootLoop_step c z _ false h2, hp]
    exact BitcoinMerkle.rootLoop_fst c z _ _ _
  · rw [BitcoinMerkle.rootLoop_step c z _ false h2, hq]
    simp only [Bool.or_true]
    exact BitcoinMerkle.rootLoop_sticky c z _

/-- General form of CVE-2012-2459: duplicating an aligned block of `2 ^ k` leaves at the end of
the list leaves the root unchanged and is detected by the mutation flag. -/
theorem BitcoinMerkle.dup_block {H : Type} [DecidableEq H] (c : H → H → H) (z : H) :
    ∀ (k : Nat) (l t : List H), l ≠ [] → l.length % 2 ^ (k + 1) = 0 → t.length = 2 ^ k →
      (BitcoinMerkle.computeMerkleRoot c z (l ++ t)).1 = (BitcoinMerkle.computeMerkleRoot c z (l ++ t ++ t)).1 ∧
      (BitcoinMerkle.computeMerkleRoot c z (l ++ t ++ t)).2 = true := by
  suffices key : ∀ (k : Nat) (l t : List H) (m : Bool), l ≠ [] → l.length % 2 ^ (k + 1) = 0 → t.length = 2 ^ k →
      (rootLoop c z (l ++ t) m).1 = (rootLoop c z (l ++ t ++ t) m).1 ∧
      (rootLoop c z (l ++ t ++ t) m).2 = true by
    intro k l t hne hl ht
    exact key k l t false hne hl ht
  intro k
  induction k with
  | zero =>
    intro l t m hne hl ht
    simp only [Nat.zero_add, Nat.pow_one, Nat.pow_zero] at hl ht
    rcases t with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simp at ht
    rotate_left
    · simp at ht
    have hlen : 0 < l.length := List.length_pos_iff.2 hne
    have hp : pairUp c (l ++ [a]) = pairUp c (l ++ [a, a]) := by
      rw [BitcoinMerkle.pairUp_append_even c l [a] hl, BitcoinMerkle.pairUp_append_even c l [a, a] hl]
      simp [pairUp]
    have hq : hasEqualPair (l ++ [a, a]) = true := by
      rw [BitcoinMerkle.hasEqualPair_append_even l [a, a] hl]
      simp [hasEqualPair]
    have e : l ++ [a] ++ [a] = l ++ [a, a] := by simp
    have h1 : 1 < (l ++ [a]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have h2 : 1 < (l ++ [a, a]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [e]
    constructor
    · rw [BitcoinMerkle.rootLoop_step c z _ m h1, BitcoinMerkle.rootLoop_step c z _ m h2, hp]
      exact BitcoinMerkle.rootLoop_fst c z _ _ _
    · rw [BitcoinMerkle.rootLoop_step c z _ m h2, hq]
      simp only [Bool.or_true]
      exact BitcoinMerkle.rootLoop_sticky c z _
  | succ k ih =>
    intro l t m hne hl ht
    have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 := Nat.pow_succ ..
    have hteven : t.length % 2 = 0 := by rw [ht, Nat.pow_succ]; simp
    rw [hpow] at hl
    have hdvd : 2 ∣ 2 ^ (k + 1) * 2 := ⟨2 ^ (k + 1), Nat.mul_comm _ _⟩
    have hleven : l.length % 2 = 0 := by
      rw [← Nat.mod_mod_of_dvd l.length hdvd, hl]
    have hlen : 0 < l.length := List.length_pos_iff.2 hne
    have htpos : 0 < t.length := by rw [ht]; exact Nat.two_pow_pos _
    have hl' : (pairUp c l).length % 2 ^ (k + 1) = 0 := by
      rw [pairUp_length]
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hl
      rw [hq]
      have e : 2 ^ (k + 1) * 2 * q + 1 = 2 * (2 ^ (k + 1) * q) + 1 := by
        rw [Nat.mul_comm (2 ^ (k + 1)) 2, Nat.mul_assoc]
      rw [e, Nat.mul_add_div (by decide), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero,
        Nat.mul_mod_right]
    have ht' : (pairUp c t).length = 2 ^ k := by
      rw [pairUp_length, ht, Nat.pow_succ]; omega
    have hne' : pairUp c l ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [pairUp_length] at this
      simp at this
      omega
    have hp1 : pairUp c (l ++ t) = pairUp c l ++ pairUp c t :=
      BitcoinMerkle.pairUp_append_even c l t hleven
    have hlt_even : (l ++ t).length % 2 = 0 := by
      simp only [List.length_append]; omega
    have hp2 : pairUp c (l ++ t ++ t) = pairUp c l ++ pairUp c t ++ pairUp c t := by
      rw [BitcoinMerkle.pairUp_append_even c (l ++ t) t hlt_even, hp1]
    have h1 : 1 < (l ++ t).length := by
      simp only [List.length_append]; omega
    have h2 : 1 < (l ++ t ++ t).length := by
      simp only [List.length_append]; omega
    obtain ⟨ihr, ihm⟩ := ih (pairUp c l) (pairUp c t) (m || hasEqualPair (l ++ t ++ t)) hne' hl' ht'
    constructor
    · rw [BitcoinMerkle.rootLoop_step c z _ m h1, BitcoinMerkle.rootLoop_step c z _ m h2, hp1, hp2]
      rw [BitcoinMerkle.rootLoop_fst c z _ (m || hasEqualPair (l ++ t)) (m || hasEqualPair (l ++ t ++ t))]
      exact ihr
    · rw [BitcoinMerkle.rootLoop_step c z _ m h2, hp2]
      exact ihm
