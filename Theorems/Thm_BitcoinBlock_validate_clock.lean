import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.validate_clock (S : ChainState) (b : BitcoinSer.Block) (now now' : Int)
    (h : BitcoinBlock.validate S b now ≠ .futureTime) (hle : now ≤ now') :
    BitcoinBlock.validate S b now' = BitcoinBlock.validate S b now := by sorry
