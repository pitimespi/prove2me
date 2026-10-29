import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.disconnectChain_connectChain (bs : List (BitcoinSer.Block × Int)) :
    ∀ (S : ChainState), BitcoinBlockV2.Reachable S → BitcoinReorg.FreshChain S bs →
    ∀ (T : ChainState) (undos : List BlockUndo), BitcoinReorg.connectChain S bs = some (T, undos) →
    ∃ S', BitcoinReorg.disconnectChain T ((bs.map Prod.fst).zip undos).reverse = some (S', true) ∧
      BitcoinReorg.StateEquiv S' S := by sorry
