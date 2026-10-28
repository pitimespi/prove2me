import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.connectBlock_iff (S : ChainState) (b : BitcoinSer.Block) (hne : b.vtx ≠ [])
    (hpos : ∀ tx ∈ b.vtx, 0 ≤ BitcoinBlockV2.valueOut tx) :
    (∃ r, BitcoinBlockV2.connectBlock S b = some r) ↔ BitcoinBlockV2.LedgerSpec S b := by sorry
