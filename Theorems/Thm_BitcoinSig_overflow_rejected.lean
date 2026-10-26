import Definitions.Def_BitcoinSig
open BitcoinSig BitcoinSer

theorem BitcoinSig.overflow_rejected (pk hash sig : Bytes) (h : BitcoinSig.parseDerLax sig = some (0, 0)) :
    BitcoinSig.pubkeyVerify pk hash sig = false := by sorry
