import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.validate_clock (S : ChainState) (b : BitcoinSer.Block) (now now' : Int)
    (h : BitcoinBlockV2.validate S b now ≠ .futureTime) (hle : now ≤ now') :
    BitcoinBlockV2.validate S b now' = BitcoinBlockV2.validate S b now := by sorry
