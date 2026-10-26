import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.calculated_bounds (version flags : BitVec 32)
    (ctx : BitcoinBIP68.Context) (inputs : List BitcoinBIP68.Input)
    (hctx : BitcoinBIP68.admissible ctx inputs)
    (hsafe : BitcoinBIP68.noOverflow version flags ctx inputs) :
    let result := BitcoinBIP68.calculate version flags ctx inputs
    (-1 ≤ result.minHeight ∧ result.minHeight ≤ (BitcoinBIP68.int32Max : Int)) ∧
    (-1 ≤ result.minTime ∧ result.minTime ≤ (BitcoinBIP68.int64Max : Int)) := by sorry
