import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_take (times : List Int) :
    BitcoinHeader.medianTimePast times = BitcoinHeader.medianTimePast (times.take BitcoinHeader.nMedianTimeSpan) := by sorry
