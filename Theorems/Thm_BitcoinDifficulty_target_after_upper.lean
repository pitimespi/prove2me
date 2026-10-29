import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.target_after_upper (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit) :
    ∀ (periods : List (Int × Int)),
    BitcoinPow.setCompact (BitcoinDifficulty.targetAfter bits periods) ≤ 4 ^ periods.length * BitcoinPow.setCompact bits := by sorry
