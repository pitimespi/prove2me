import Definitions.Def_BitcoinHeader

open BitcoinHeader

theorem solution (times : List Int) :
    BitcoinHeader.medianTimePast times = BitcoinHeader.medianTimePast (times.take BitcoinHeader.nMedianTimeSpan) := by
  unfold medianTimePast timeWindow
  rw [List.take_take, Nat.min_self]
