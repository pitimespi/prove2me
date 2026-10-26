import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.connectBlock_apply (S : ChainState) (b : BitcoinSer.Block) (u : Ledger) (undo : BlockUndo)
    (h : BitcoinBlock.connectBlock S b = some (u, undo)) : u = (BitcoinBlock.applySpec S b).utxo := by sorry
