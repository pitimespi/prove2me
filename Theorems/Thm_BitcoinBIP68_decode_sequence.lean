import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.decode_sequence (sequence : BitVec 32) :
    (BitcoinBIP68.coreDisabled sequence = true ↔ BitcoinBIP68.specDisabled sequence) ∧
    (BitcoinBIP68.coreTimeBased sequence = true ↔ BitcoinBIP68.specTimeBased sequence) ∧
    BitcoinBIP68.coreDelay sequence = BitcoinBIP68.specDelay sequence ∧
    BitcoinBIP68.coreSeconds sequence = 512 * BitcoinBIP68.specDelay sequence := by sorry
