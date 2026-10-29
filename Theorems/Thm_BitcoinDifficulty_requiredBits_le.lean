import Definitions.Def_BitcoinDifficulty
import Definitions.Def_BitcoinPow
open BitcoinDifficulty BitcoinPow

theorem BitcoinDifficulty.requiredBits_le (S : BitcoinBlockV2.ChainState)
    (hb : BitcoinPow.setCompact (BitVec.ofNat 32 S.tip.bits) ≤ BitcoinPow.powLimit) :
    BitcoinPow.setCompact S.requiredBits ≤ 4 * BitcoinPow.setCompact (BitVec.ofNat 32 S.tip.bits) := by sorry
