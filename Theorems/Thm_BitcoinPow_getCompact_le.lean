import Definitions.Def_BitcoinPow

theorem BitcoinPow.getCompact_le (v : Nat) (hv : v < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ v := by sorry
