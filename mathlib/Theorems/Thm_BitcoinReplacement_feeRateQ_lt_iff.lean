import Definitions.Def_BitcoinReplacement

theorem BitcoinReplacement.feeRateQ_lt_iff (a b : BitcoinReplacement.Tx) :
    a.feeRateQ < b.feeRateQ ↔ BitcoinReplacement.FeeRate.lt a.feeRate b.feeRate := by sorry
