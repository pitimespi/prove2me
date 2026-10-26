import Definitions.Def_BitcoinPow

theorem BitcoinPow.getCompact_valid (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.compactNegative (BitcoinPow.getCompact v) = false ∧
    BitcoinPow.compactOverflow (BitcoinPow.getCompact v) = false := by sorry
