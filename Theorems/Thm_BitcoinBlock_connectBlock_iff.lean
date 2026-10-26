import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.connectBlock_iff (S : ChainState) (b : BitcoinSer.Block) (hne : b.vtx ≠ [])
    (hpos : ∀ tx ∈ b.vtx, 0 ≤ BitcoinBlock.valueOut tx) :
    (∃ r, BitcoinBlock.connectBlock S b = some r) ↔ BitcoinBlock.LedgerSpec S b := by sorry
