import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.work_increases (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : BitcoinBlock.validate S b now = .accept S' undo) : S.chainWork < S'.chainWork := by sorry
