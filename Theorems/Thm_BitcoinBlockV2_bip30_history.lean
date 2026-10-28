import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader

theorem BitcoinBlockV2.bip30_history (S : ChainState) (height : Nat) (hash : BitcoinSer.Bytes) :
    BitcoinBlockV2.bip30Checked S height hash = false ↔
      height < BIP34_IMPLIES_BIP30_LIMIT ∧
      (BitcoinBlockV2.isBIP30Repeat height hash = true ∨
        ∃ h, S.headers[BitcoinHeader.BIP34Height]? = some h ∧ BitcoinSer.headerHash h = BitcoinBlockV2.bip34Hash) := by sorry
