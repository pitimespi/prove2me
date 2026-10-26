import Definitions.Def_BitcoinBlock
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader

theorem BitcoinBlock.bip30_history (S : ChainState) (height : Nat) (hash : BitcoinSer.Bytes) :
    BitcoinBlock.bip30Checked S height hash = false ↔
      height < BIP34_IMPLIES_BIP30_LIMIT ∧
      (BitcoinBlock.isBIP30Repeat height hash = true ∨
        ∃ h, S.headers[BitcoinHeader.BIP34Height]? = some h ∧ BitcoinSer.headerHash h = BitcoinBlock.bip34Hash) := by sorry
