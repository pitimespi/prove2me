import Definitions.Def_BitcoinActivation

theorem BitcoinActivation.lockTimeFlags_eq (height : Nat) :
    BitcoinActivation.lockTimeFlags height =
      if 419328 ≤ height then BitcoinActivation.LOCKTIME_VERIFY_SEQUENCE else 0 := by sorry
