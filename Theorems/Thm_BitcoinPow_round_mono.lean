import Definitions.Def_BitcoinPow

theorem BitcoinPow.round_mono (v w : Nat) (hvw : v ≤ w) (hw : w < BitcoinPow.width) :
    BitcoinPow.setCompact (BitcoinPow.getCompact v) ≤ BitcoinPow.setCompact (BitcoinPow.getCompact w) := by sorry
