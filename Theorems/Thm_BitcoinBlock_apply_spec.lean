import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.apply_spec (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : BitcoinBlock.validate S b now = .accept S' undo) : S' = BitcoinBlock.applySpec S b := by sorry
