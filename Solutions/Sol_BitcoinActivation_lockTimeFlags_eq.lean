import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- Sequence locks are verified exactly from the CSV activation height. -/
theorem solution (height : Nat) :
    BitcoinActivation.lockTimeFlags height =
      if 419328 ≤ height then BitcoinActivation.LOCKTIME_VERIFY_SEQUENCE else 0 := by
  unfold lockTimeFlags activeAt deploymentHeight
  simp
