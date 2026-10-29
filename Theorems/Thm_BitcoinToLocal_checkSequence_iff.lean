import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.checkSequence_iff (tx : BitcoinSer.Tx) (nIn : Nat) (delay : Int) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16) :
    BitcoinSig.checkSequence tx nIn delay = true ↔
      2 ≤ tx.version ∧
      BitcoinToLocal.inputSequence tx nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      BitcoinToLocal.inputSequence tx nIn &&& (BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ||| BitcoinSig.SEQUENCE_LOCKTIME_MASK) <
        BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ∧
      delay.toNat ≤ BitcoinToLocal.inputSequence tx nIn &&& (BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ||| BitcoinSig.SEQUENCE_LOCKTIME_MASK) := by sorry
