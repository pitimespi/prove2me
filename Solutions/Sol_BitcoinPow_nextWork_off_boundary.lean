import Definitions.Def_BitcoinPow

open BitcoinPow

theorem solution (lastHeight : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (h : (lastHeight + 1) % BitcoinPow.difficultyAdjustmentInterval ≠ 0) :
    BitcoinPow.nextWorkRequired lastHeight lastBits lastTime firstTime = lastBits ∧
    BitcoinPow.permittedTransition (lastHeight + 1) lastBits lastBits = true := by
  constructor
  · unfold nextWorkRequired; rw [if_pos h]
  · unfold permittedTransition; rw [if_neg h]; simp
