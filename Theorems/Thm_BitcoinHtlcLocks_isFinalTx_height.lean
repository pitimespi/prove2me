import Definitions.Def_BitcoinHtlcLocks
import Definitions.Def_BitcoinSer
open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

theorem BitcoinHtlcLocks.isFinalTx_height (tx : BitcoinSer.Tx) (height : Nat) (blockTime : Int)
    (hl : BitcoinHtlcLocks.HeightLocked tx) (i : Nat) (hi : i < tx.vin.length)
    (hseq : (tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩).nSequence ≠ BitcoinBlockV2.SEQUENCE_FINAL) :
    BitcoinBlockV2.isFinalTx tx height blockTime = true ↔ tx.nLockTime < height := by sorry
