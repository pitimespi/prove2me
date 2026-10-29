import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.reorg_safety (S : ChainState) (hR : BitcoinBlockV2.Reachable S)
    (bs : List (BitcoinSer.Block × Int)) (hF : BitcoinReorg.FreshChain S bs)
    (T : ChainState) (undos : List BlockUndo) (hc : BitcoinReorg.connectChain S bs = some (T, undos))
    (S' : ChainState) (clean : Bool)
    (hd : BitcoinReorg.disconnectChain T ((bs.map Prod.fst).zip undos).reverse = some (S', clean))
    (cs : List (BitcoinSer.Block × Int)) (U : ChainState) (undos' : List BlockUndo)
    (hc' : BitcoinReorg.connectChain S' cs = some (U, undos')) :
    clean = true ∧ ∃ U₀, BitcoinReorg.connectChain S cs = some (U₀, undos') ∧ BitcoinReorg.StateEquiv U U₀ ∧
      BitcoinBlockV2.Reachable U₀ := by sorry
