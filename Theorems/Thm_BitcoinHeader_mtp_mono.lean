import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_mono (times : List Int) (t : Int)
    (h : BitcoinHeader.medianTimePast times < t) :
    BitcoinHeader.medianTimePast times ≤ BitcoinHeader.medianTimePast (t :: times) := by sorry
