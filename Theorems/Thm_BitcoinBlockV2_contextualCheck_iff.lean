import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.contextualCheck_iff (S : ChainState) (b : BitcoinSer.Block)
    (hne : b.vtx ≠ []) (hvin : ∀ tx ∈ b.vtx, tx.vin ≠ []) :
    BitcoinBlockV2.contextualCheckBlock S b = true ↔ BitcoinBlockV2.ContextSpec S b := by sorry
