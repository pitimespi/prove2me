import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.raw_target_bounds (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (lastTime firstTime : Int) :
    BitcoinDifficulty.rawNextTarget t lastTime firstTime ≤ 4 * t ∧
    (BitcoinDifficulty.rawNextTarget t lastTime firstTime = BitcoinPow.powLimit ∨
      t / 4 ≤ BitcoinDifficulty.rawNextTarget t lastTime firstTime) := by sorry
