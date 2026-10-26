import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.futureTime_transient (S : ChainState) (b : BitcoinSer.Block) (now : Int)
    (h : BitcoinBlock.validate S b now = .futureTime) (now' : Int)
    (hle : (b.header.time : Int) ≤ now' + MAX_FUTURE_BLOCK_TIME) :
    BitcoinBlock.validate S b now' ≠ .futureTime ∧
    BitcoinBlock.validate S b now' = BitcoinBlock.validate S b ((b.header.time : Int) - MAX_FUTURE_BLOCK_TIME) := by sorry
