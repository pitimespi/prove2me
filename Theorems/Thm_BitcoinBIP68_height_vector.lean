import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.height_vector (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input) :
    BitcoinBIP68.returnedHeights (BitcoinBIP68.calculate version flags ctx inputs) =
      BitcoinBIP68.expectedHeights version flags inputs := by sorry
