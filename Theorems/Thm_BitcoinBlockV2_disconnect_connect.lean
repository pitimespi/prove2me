import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

theorem BitcoinBlockV2.disconnect_connect (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hwf : BitcoinBlockV2.WellFormed S) (hnd : (b.vtx.map BitcoinSer.txid).Nodup)
    (hfresh : ∀ tx ∈ b.vtx, ∀ o, BitcoinBlockV2.getCoin S.utxo ⟨BitcoinSer.txid tx, o⟩ = none)
    (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) :
    ∃ u, BitcoinBlockV2.disconnectBlock S'.utxo S.nextHeight (BitcoinSer.headerHash b.header) b undo = some (u, true) ∧
      BitcoinBlockV2.Equiv u S.utxo := by sorry
