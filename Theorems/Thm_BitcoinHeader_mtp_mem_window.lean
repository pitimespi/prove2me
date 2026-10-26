import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_mem_window (times : List Int) (h : times ≠ []) :
    BitcoinHeader.medianTimePast times ∈ BitcoinHeader.timeWindow times := by sorry
