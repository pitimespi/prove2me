import Definitions.Def_BitcoinPow

theorem BitcoinPow.clamp_bounds (actual : Int) :
    ((BitcoinPow.targetTimespan / 4 : Nat) : Int) ≤ BitcoinPow.clampTimespan actual ∧
    BitcoinPow.clampTimespan actual ≤ ((BitcoinPow.targetTimespan * 4 : Nat) : Int) := by sorry
