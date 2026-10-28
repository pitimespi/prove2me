import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.checkTransaction_iff (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.checkTransaction tx = true ↔ BitcoinBlockV2.TxSpec tx := by sorry
