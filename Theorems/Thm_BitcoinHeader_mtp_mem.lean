import Definitions.Def_BitcoinHeader

theorem BitcoinHeader.mtp_mem (times : List Int) (h : times ≠ []) :
    BitcoinHeader.medianTimePast times ∈ times := by sorry
