import Definitions.Def_BitcoinPow

theorem BitcoinPow.overflow_iff (c : BitVec 32) :
    BitcoinPow.compactOverflow c = true ↔ BitcoinPow.width ≤ BitcoinPow.specTarget c := by sorry
