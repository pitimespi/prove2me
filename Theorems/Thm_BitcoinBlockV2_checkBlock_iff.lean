import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.checkBlock_iff (b : BitcoinSer.Block) :
    BitcoinBlockV2.checkBlock b = true ↔ BitcoinBlockV2.checkHeaderPow b.header = true ∧ BitcoinBlockV2.BlockSpec b := by sorry
