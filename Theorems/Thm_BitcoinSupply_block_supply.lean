import Definitions.Def_BitcoinSupply
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSubsidy
open BitcoinSupply BitcoinBlockV2

theorem BitcoinSupply.block_supply (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hR : BitcoinBlockV2.Reachable S) (hv : BitcoinBlockV2.validate S b now = .accept S' undo) :
    BitcoinSupply.totalValue S'.utxo ≤
      BitcoinSupply.totalValue S.utxo + (BitcoinSubsidy.coreSubsidy S.nextHeight : Int) := by sorry
