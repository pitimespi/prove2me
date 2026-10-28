import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.connectBlock_apply (S : ChainState) (b : BitcoinSer.Block) (u : Ledger) (undo : BlockUndo)
    (h : BitcoinBlockV2.connectBlock S b = some (u, undo)) : u = (BitcoinBlockV2.applySpec S b).utxo := by sorry
