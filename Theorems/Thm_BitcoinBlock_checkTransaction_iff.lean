import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.checkTransaction_iff (tx : BitcoinSer.Tx) :
    BitcoinBlock.checkTransaction tx = true ↔ BitcoinBlock.TxSpec tx := by sorry
