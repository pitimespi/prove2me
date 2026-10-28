import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.work_increases (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) : S.chainWork < S'.chainWork := by sorry
