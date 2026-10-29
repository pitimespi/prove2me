import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

theorem BitcoinReorg.consistent_connectChain (S : ChainState) (hS : BitcoinReorg.Consistent S)
    (cs : List (BitcoinSer.Block × Int)) (U : ChainState) (undos : List BlockUndo)
    (h : BitcoinReorg.connectChain S cs = some (U, undos)) : BitcoinReorg.Consistent U := by sorry
