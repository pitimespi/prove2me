import Definitions.Def_BitcoinPow

theorem BitcoinPow.nextWork_permitted (height : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int)
    (hh : height % BitcoinPow.difficultyAdjustmentInterval = 0)
    (hold : BitcoinPow.setCompact lastBits ≤ BitcoinPow.powLimit) :
    BitcoinPow.permittedTransition height lastBits
      (BitcoinPow.calculateNextWork lastBits lastTime firstTime) = true := by sorry
