import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.connectChain_reachable (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    ∀ (bs : List (BitcoinSer.Block × Int)) (T : ChainState) (undos : List BlockUndo),
    BitcoinReorg.connectChain S bs = some (T, undos) → BitcoinBlockV2.Reachable T := by sorry
