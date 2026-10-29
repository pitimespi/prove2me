import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinToLocal
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.checkLockTime_iff (tx : BitcoinSer.Tx) (nIn : Nat) (expiry : Int) (h0 : 0 ≤ expiry)
    (hT : expiry < 500000000) :
    BitcoinSig.checkLockTime tx nIn expiry = true ↔
      tx.nLockTime < 500000000 ∧ expiry ≤ (tx.nLockTime : Int) ∧ BitcoinToLocal.inputSequence tx nIn ≠ 0xffffffff := by sorry
