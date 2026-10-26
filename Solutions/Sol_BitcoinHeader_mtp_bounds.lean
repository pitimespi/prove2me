import Definitions.Def_BitcoinHeader
import Theorems.Thm_BitcoinHeader_mtp_mem_window

open BitcoinHeader

theorem solution (times : List Int) (h : times ≠ []) (lo hi : Int)
    (hb : ∀ t ∈ BitcoinHeader.timeWindow times, lo ≤ t ∧ t ≤ hi) :
    lo ≤ BitcoinHeader.medianTimePast times ∧ BitcoinHeader.medianTimePast times ≤ hi :=
  hb _ (BitcoinHeader.mtp_mem_window times h)
