import Definitions.Def_BitcoinPow

theorem BitcoinPow.nextWork_off_boundary (lastHeight : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (h : (lastHeight + 1) % BitcoinPow.difficultyAdjustmentInterval ≠ 0) :
    BitcoinPow.nextWorkRequired lastHeight lastBits lastTime firstTime = lastBits ∧
    BitcoinPow.permittedTransition (lastHeight + 1) lastBits lastBits = true := by sorry
