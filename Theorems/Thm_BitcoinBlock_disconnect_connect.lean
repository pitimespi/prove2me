import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer

theorem BitcoinBlock.disconnect_connect (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hwf : BitcoinBlock.WellFormed S) (hnd : (b.vtx.map BitcoinSer.txid).Nodup)
    (hfresh : ∀ tx ∈ b.vtx, ∀ o, BitcoinBlock.getCoin S.utxo ⟨BitcoinSer.txid tx, o⟩ = none)
    (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash)
    (h : BitcoinBlock.validate S b now = .accept S' undo) :
    ∃ u, BitcoinBlock.disconnectBlock S'.utxo S.nextHeight (BitcoinSer.headerHash b.header) b undo = some (u, true) ∧
      BitcoinBlock.Equiv u S.utxo := by sorry
