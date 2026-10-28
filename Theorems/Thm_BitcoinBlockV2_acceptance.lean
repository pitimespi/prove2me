import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.acceptance (S : ChainState) (b : BitcoinSer.Block) (now : Int) (hR : BitcoinBlockV2.Reachable S) :
    BitcoinBlockV2.accepts S b now ↔ BitcoinBlockV2.Valid S b now := by sorry
