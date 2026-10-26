import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_mono_chain (times : List Int)
    (hok : ∀ (i : Nat) (hi : i < times.length),
      BitcoinHeader.medianTimePast (times.drop (i + 1)) < times[i]) :
    ∀ (i j : Nat), i ≤ j → j ≤ times.length →
      BitcoinHeader.medianTimePast (times.drop j) ≤ BitcoinHeader.medianTimePast (times.drop i) := by sorry
