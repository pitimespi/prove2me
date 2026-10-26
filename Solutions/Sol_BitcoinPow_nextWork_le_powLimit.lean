import Definitions.Def_BitcoinPow
import Theorems.Thm_BitcoinPow_getCompact_le

open BitcoinPow

private theorem powLimit_lt_width : powLimit < width := by
  unfold powLimit width
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide) (by decide))

/-- The capped value never exceeds the proof-of-work limit. -/
private theorem cap_le (x : Nat) : (if powLimit < x then powLimit else x) ≤ powLimit := by
  split <;> omega

theorem solution (lastBits : BitVec 32) (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.calculateNextWork lastBits lastTime firstTime) ≤ BitcoinPow.powLimit := by
  unfold calculateNextWork
  simp only []
  have hcap := cap_le ((setCompact lastBits * (clampTimespan (lastTime - firstTime)).toNat % width) / targetTimespan)
  exact Nat.le_trans (BitcoinPow.getCompact_le _ (Nat.lt_of_le_of_lt hcap powLimit_lt_width)) hcap
