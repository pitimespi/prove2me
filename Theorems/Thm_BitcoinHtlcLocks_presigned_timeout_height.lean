import Definitions.Def_BitcoinHtlcLocks
import Definitions.Def_BitcoinSer
open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

theorem BitcoinHtlcLocks.presigned_timeout_height (tx : BitcoinSer.Tx) (expiry height : Nat) (blockTime : Int)
    (hexp : 0 < expiry ∧ expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (htx : tx.nLockTime = expiry)
    (i : Nat) (hi : i < tx.vin.length)
    (hseq : (tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩).nSequence ≠ BitcoinBlockV2.SEQUENCE_FINAL)
    (hfinal : BitcoinBlockV2.isFinalTx tx height blockTime = true) : expiry < height := by sorry
