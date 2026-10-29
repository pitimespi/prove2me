import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.no_wrap (t : Nat) (ht : t ≤ BitcoinPow.powLimit) (ts : Nat) (hts : ts ≤ 4838400) :
    t * ts < BitcoinPow.width := by sorry
