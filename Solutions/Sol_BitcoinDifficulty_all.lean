import Definitions.Def_BitcoinDifficulty
import Theorems.Thm_BitcoinPow_clamp_bounds
import Theorems.Thm_BitcoinPow_getCompact_le
import Theorems.Thm_BitcoinPow_nextWork_le_powLimit
import Theorems.Thm_BitcoinPow_round_mono

open BitcoinDifficulty BitcoinPow

private theorem clamp_nat_bounds (actual : Int) :
    302400 ≤ (clampTimespan actual).toNat ∧ (clampTimespan actual).toNat ≤ 4838400 := by
  have h := BitcoinPow.clamp_bounds actual
  simp only [targetTimespan] at h
  omega

/-- The product of a valid target and the clamped timespan never wraps around `2^256`. -/
theorem BitcoinDifficulty.no_wrap (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (ts : Nat) (hts : ts ≤ 4838400) :
    t * ts < BitcoinPow.width := by
  simp only [powLimit] at ht
  simp only [width]
  have h1 : t * ts ≤ (2 ^ 224 - 1) * 4838400 := Nat.mul_le_mul ht hts
  have h2 : (2 ^ 224 - 1) * 4838400 < 2 ^ 256 := by decide
  omega

/-- **The raw target moves by at most a factor of four.** For a last target `t ≤ powLimit` and any
timestamps: `t / 4 ≤ rawNextTarget t lastTime firstTime` unless the cap binds, and
`rawNextTarget t lastTime firstTime ≤ 4 * t`. -/
theorem BitcoinDifficulty.raw_target_bounds (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (lastTime firstTime : Int) :
    BitcoinDifficulty.rawNextTarget t lastTime firstTime ≤ 4 * t ∧
    (BitcoinDifficulty.rawNextTarget t lastTime firstTime = BitcoinPow.powLimit ∨
      t / 4 ≤ BitcoinDifficulty.rawNextTarget t lastTime firstTime) := by
  have hT : targetTimespan = 1209600 := rfl
  simp only [rawNextTarget, hT]
  obtain ⟨hlo, hhi⟩ := clamp_nat_bounds (lastTime - firstTime)
  have hnw := BitcoinDifficulty.no_wrap t ht _ hhi
  rw [Nat.mod_eq_of_lt hnw]
  -- upper: t * ts / 1209600 ≤ t * 4838400 / 1209600 = 4 t
  have hup : t * (clampTimespan (lastTime - firstTime)).toNat / 1209600 ≤ 4 * t := by
    apply Nat.div_le_of_le_mul
    have := Nat.mul_le_mul_left t hhi
    omega
  -- lower: t * ts / 1209600 ≥ t * 302400 / 1209600 = t / 4
  have hlow : t / 4 ≤ t * (clampTimespan (lastTime - firstTime)).toNat / 1209600 := by
    have h4 : t / 4 = t * 302400 / 1209600 := by
      rw [show (1209600 : Nat) = 302400 * 4 by rfl, show t * 302400 = 302400 * t by omega]
      rw [Nat.mul_div_mul_left _ _ (by decide)]
    rw [h4]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left t hlo)
  constructor
  · split
    · omega
    · exact hup
  · split
    · exact Or.inl rfl
    · exact Or.inr hlow

private theorem calculateNextWork_eq (bits : BitVec 32) (lastTime firstTime : Int) :
    calculateNextWork bits lastTime firstTime = getCompact (rawNextTarget (setCompact bits) lastTime firstTime) := rfl

private theorem raw_lt_width (t : Nat) (ht : t ≤ powLimit) (lastTime firstTime : Int) :
    rawNextTarget t lastTime firstTime < width := by
  have h := (BitcoinDifficulty.raw_target_bounds t ht lastTime firstTime).1
  simp only [powLimit, width] at ht ⊢
  omega

/-- **The encoded target at most quadruples per period**, whatever the timestamps. -/
theorem BitcoinDifficulty.encoded_target_upper (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit)
    (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork bits lastTime firstTime) ≤ 4 * BitcoinPow.setCompact bits := by
  rw [calculateNextWork_eq]
  have h1 := BitcoinPow.getCompact_le _ (raw_lt_width _ hb lastTime firstTime)
  have h2 := (BitcoinDifficulty.raw_target_bounds _ hb lastTime firstTime).1
  omega

/-- **The encoded target drops by at most a factor of four per period**, up to the compact
rounding: the new target is at least the encoding of a quarter of the old one. -/
theorem BitcoinDifficulty.encoded_target_lower (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit)
    (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.getCompact (BitcoinPow.setCompact bits / 4)) ≤
      BitcoinPow.setCompact (BitcoinPow.calculateNextWork bits lastTime firstTime) := by
  rw [calculateNextWork_eq]
  have hw := raw_lt_width _ hb lastTime firstTime
  rcases (BitcoinDifficulty.raw_target_bounds _ hb lastTime firstTime).2 with hcap | hlow
  · rw [hcap]
    apply BitcoinPow.round_mono
    · have := Nat.div_le_self (setCompact bits) 4; omega
    · simp only [powLimit, width]; decide
  · exact BitcoinPow.round_mono _ _ hlow hw

/-- Over `m` periods the encoded target grows by at most `4^m`, whatever the timestamps. -/
theorem BitcoinDifficulty.target_after_upper (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit) :
    ∀ (periods : List (Int × Int)),
    BitcoinPow.setCompact (BitcoinDifficulty.targetAfter bits periods) ≤ 4 ^ periods.length * BitcoinPow.setCompact bits := by
  intro periods
  induction periods generalizing bits with
  | nil => simp [targetAfter]
  | cons p rest ih =>
    obtain ⟨lt, ft⟩ := p
    simp only [targetAfter, List.length_cons]
    have hb' := BitcoinPow.nextWork_le_powLimit bits lt ft
    have h1 := ih (calculateNextWork bits lt ft) hb'
    have h2 := BitcoinDifficulty.encoded_target_upper bits hb lt ft
    calc setCompact (targetAfter (calculateNextWork bits lt ft) rest)
        ≤ 4 ^ rest.length * setCompact (calculateNextWork bits lt ft) := h1
      _ ≤ 4 ^ rest.length * (4 * setCompact bits) := Nat.mul_le_mul_left _ h2
      _ = 4 ^ (rest.length + 1) * setCompact bits := by rw [Nat.pow_succ, Nat.mul_assoc]

/-- The target never exceeds `powLimit` after any number of periods. -/
theorem BitcoinDifficulty.target_after_le_powLimit (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit) :
    ∀ (periods : List (Int × Int)), BitcoinPow.setCompact (BitcoinDifficulty.targetAfter bits periods) ≤ BitcoinPow.powLimit := by
  intro periods
  induction periods generalizing bits with
  | nil => simpa [targetAfter] using hb
  | cons p rest ih =>
    obtain ⟨lt, ft⟩ := p
    simp only [targetAfter]
    exact ih _ (BitcoinPow.nextWork_le_powLimit bits lt ft)

/-- **Timewarp bound.** On a chain whose tip is at a retarget boundary with a valid target, the
required target of the next block is at most four times the tip's target, whatever the block
timestamps were (`ChainState.requiredBits` of the block mission). -/
theorem BitcoinDifficulty.requiredBits_le (S : BitcoinBlockV2.ChainState)
    (hb : BitcoinPow.setCompact (BitVec.ofNat 32 S.tip.bits) ≤ BitcoinPow.powLimit) :
    BitcoinPow.setCompact S.requiredBits ≤ 4 * BitcoinPow.setCompact (BitVec.ofNat 32 S.tip.bits) := by
  simp only [BitcoinBlockV2.ChainState.requiredBits, nextWorkRequired]
  split
  · omega
  · exact BitcoinDifficulty.encoded_target_upper _ hb _ _
