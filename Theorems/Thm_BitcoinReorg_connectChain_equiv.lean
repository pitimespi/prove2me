import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.connectChain_equiv (bs : List (BitcoinSer.Block × Int)) :
    ∀ (S T : ChainState), BitcoinReorg.StateEquiv S T →
    (BitcoinReorg.connectChain S bs = none ∧ BitcoinReorg.connectChain T bs = none) ∨
    (∃ U V undos, BitcoinReorg.connectChain S bs = some (U, undos) ∧ BitcoinReorg.connectChain T bs = some (V, undos) ∧
      BitcoinReorg.StateEquiv U V) := by sorry
