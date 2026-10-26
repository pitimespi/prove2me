import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.contextualCheck_iff (S : ChainState) (b : BitcoinSer.Block)
    (hne : b.vtx ≠ []) (hvin : ∀ tx ∈ b.vtx, tx.vin ≠ []) :
    BitcoinBlock.contextualCheckBlock S b = true ↔ BitcoinBlock.ContextSpec S b := by sorry
