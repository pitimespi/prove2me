import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.acceptance (S : ChainState) (b : BitcoinSer.Block) (now : Int) (hR : BitcoinBlock.Reachable S) :
    BitcoinBlock.accepts S b now ↔ BitcoinBlock.Valid S b now := by sorry
