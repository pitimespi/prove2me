import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.normalizeS_low (s : Nat) (hs : s < BitcoinSig.n) :
    BitcoinSig.isHighS (BitcoinSig.normalizeS s) = false := by sorry
