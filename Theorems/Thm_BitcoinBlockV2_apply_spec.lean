import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.apply_spec (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) : S' = BitcoinBlockV2.applySpec S b := by sorry
