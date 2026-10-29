import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.encoded_target_lower (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit)
    (lastTime firstTime : Int) :
    BitcoinPow.setCompact (BitcoinPow.getCompact (BitcoinPow.setCompact bits / 4)) ≤
      BitcoinPow.setCompact (BitcoinPow.calculateNextWork bits lastTime firstTime) := by sorry
