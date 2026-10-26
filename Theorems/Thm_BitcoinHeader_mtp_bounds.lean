import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_bounds (times : List Int) (h : times ≠ []) (lo hi : Int)
    (hb : ∀ t ∈ BitcoinHeader.timeWindow times, lo ≤ t ∧ t ≤ hi) :
    lo ≤ BitcoinHeader.medianTimePast times ∧ BitcoinHeader.medianTimePast times ≤ hi := by sorry
