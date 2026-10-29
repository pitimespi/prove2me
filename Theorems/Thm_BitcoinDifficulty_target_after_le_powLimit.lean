import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.target_after_le_powLimit (bits : BitVec 32) (hb : BitcoinPow.setCompact bits ≤ BitcoinPow.powLimit) :
    ∀ (periods : List (Int × Int)), BitcoinPow.setCompact (BitcoinDifficulty.targetAfter bits periods) ≤ BitcoinPow.powLimit := by sorry
