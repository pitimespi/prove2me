import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.checkBlock_iff (b : BitcoinSer.Block) :
    BitcoinBlock.checkBlock b = true ↔ BitcoinBlock.checkHeaderPow b.header = true ∧ BitcoinBlock.BlockSpec b := by sorry
