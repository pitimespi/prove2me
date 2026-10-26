import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.core_correct (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input)
    (hctx : BitcoinBIP68.admissible ctx inputs)
    (hsafe : BitcoinBIP68.noOverflow version flags ctx inputs) :
    (BitcoinBIP68.sequenceLocks version flags ctx inputs = true ↔
      BitcoinBIP68.satisfiesBIP68 version flags ctx inputs) ∧
    BitcoinBIP68.returnedHeights (BitcoinBIP68.calculate version flags ctx inputs) =
      BitcoinBIP68.expectedHeights version flags inputs := by sorry
