import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.futureTime_transient (S : ChainState) (b : BitcoinSer.Block) (now : Int)
    (h : BitcoinBlockV2.validate S b now = .futureTime) (now' : Int)
    (hle : (b.header.time : Int) ≤ now' + MAX_FUTURE_BLOCK_TIME) :
    BitcoinBlockV2.validate S b now' ≠ .futureTime ∧
    BitcoinBlockV2.validate S b now' = BitcoinBlockV2.validate S b ((b.header.time : Int) - MAX_FUTURE_BLOCK_TIME) := by sorry
