import Definitions.Def_BitcoinHeader
import Theorems.Thm_BitcoinHeader_mtp_mem_window

open BitcoinHeader

theorem solution (times : List Int) (h : times ≠ []) :
    BitcoinHeader.medianTimePast times ∈ times :=
  List.mem_of_mem_take (BitcoinHeader.mtp_mem_window times h)
