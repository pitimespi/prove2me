import Definitions.Def_BitcoinPow

theorem BitcoinPow.setCompact_eq_spec (c : BitVec 32) (h : BitcoinPow.compactOverflow c = false) :
    BitcoinPow.setCompact c = BitcoinPow.specTarget c := by sorry
