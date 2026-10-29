import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.lightning_delay (tx : BitcoinSer.Tx) (nIn : Nat) (delay : Int) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16)
    (hseq : BitcoinToLocal.inputSequence tx nIn < 2 ^ 16) :
    BitcoinSig.checkSequence tx nIn delay = true ↔ 2 ≤ tx.version ∧ delay.toNat ≤ BitcoinToLocal.inputSequence tx nIn := by sorry
