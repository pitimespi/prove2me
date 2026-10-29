import Definitions.Def_BitcoinHtlcLocks
import Theorems.Thm_BitcoinHtlc_received_p2wsh_spend
import Theorems.Thm_BitcoinHtlc_cltv_concrete
import Theorems.Thm_BitcoinHtlc_checkLockTime_iff

open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

/-- `IsFinalTx` for a height-locked transaction with a non-final input: the transaction is final at
height `h` exactly when its lock time is below `h`. -/
theorem BitcoinHtlcLocks.isFinalTx_height (tx : BitcoinSer.Tx) (height : Nat) (blockTime : Int)
    (hl : BitcoinHtlcLocks.HeightLocked tx) (i : Nat) (hi : i < tx.vin.length)
    (hseq : (tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩).nSequence ≠ BitcoinBlockV2.SEQUENCE_FINAL) :
    BitcoinBlockV2.isFinalTx tx height blockTime = true ↔ tx.nLockTime < height := by
  obtain ⟨h0, hT⟩ := hl
  unfold BitcoinBlockV2.isFinalTx
  rw [if_neg (by omega), if_pos hT]
  have hall : (tx.vin.all fun i => decide (i.nSequence = BitcoinBlockV2.SEQUENCE_FINAL)) = false := by
    rw [List.all_eq_false]
    refine ⟨tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩, ?_, by simpa using hseq⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  by_cases hlt : (tx.nLockTime : Int) < (height : Int)
  · rw [if_pos hlt]; simp; omega
  · rw [if_neg hlt, hall]; simp; omega

/-- A pre-signed HTLC-timeout transaction (lock time = the expiry, a block height; the HTLC input
not final) is accepted in a block only above the expiry height. -/
theorem BitcoinHtlcLocks.presigned_timeout_height (tx : BitcoinSer.Tx) (expiry height : Nat) (blockTime : Int)
    (hexp : 0 < expiry ∧ expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (htx : tx.nLockTime = expiry)
    (i : Nat) (hi : i < tx.vin.length)
    (hseq : (tx.vin.getD i ⟨⟨[], 0⟩, [], 0, []⟩).nSequence ≠ BitcoinBlockV2.SEQUENCE_FINAL)
    (hfinal : BitcoinBlockV2.isFinalTx tx height blockTime = true) : expiry < height := by
  have := (BitcoinHtlcLocks.isFinalTx_height tx height blockTime ⟨by omega, by omega⟩ i hi hseq).1 hfinal
  omega

/-- **A received HTLC cannot be timed out before its expiry, at the consensus level.** A transaction
that spends a received HTLC output (pay-to-witness-script-hash of `receivedBytes`) with a
two-element witness `[sig, pk]`, under the `WITNESS` and `CHECKLOCKTIMEVERIFY` flags, and that is
final in a block at height `h`, is either a revocation spend or has `cltv_expiry < h`. -/
theorem BitcoinHtlcLocks.received_spend_height (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (hcltv : c.flags.cltv = true)
    (revHash remoteKey localKey payHash : BitcoinSer.Bytes) (expiry : Int) (sig pk : BitcoinSer.Bytes)
    (hrev : revHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hrem : remoteKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hloc : localKey.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hpay : payHash.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hexp : 0 < expiry ∧ expiry < BitcoinBlockV2.LOCKTIME_THRESHOLD) (hnIn : c.nIn < c.tx.vin.length)
    (hv : BitcoinVerify.verifyScript tap c []
        (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry)))
        ([sig, pk] ++ [BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry]) = true)
    (height : Nat) (blockTime : Int) (hfinal : BitcoinBlockV2.isFinalTx c.tx height blockTime = true) :
    BitcoinHtlcLocks.RevocationSpend c (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry) revHash pk sig ∨
      expiry < height := by
  have hd : expiry.natAbs < 2 ^ 32 := by
    have : expiry < 500000000 := by simpa [BitcoinBlockV2.LOCKTIME_THRESHOLD] using hexp.2
    omega
  obtain ⟨-, -, hsp⟩ := (BitcoinHtlc.received_p2wsh_spend tap c hf revHash remoteKey localKey payHash expiry [sig, pk]
    hrev hrem hloc hpay hd).1 hv
  have hrev' : ([sig, pk] : List BitcoinSer.Bytes).reverse = [pk, sig] := rfl
  rw [hrev'] at hsp
  unfold BitcoinHtlc.ReceivedSpend at hsp
  rcases hsp with ⟨pk', sig', heq, hh, hcs⟩ | ⟨pre, l, r, d, heq, -⟩ | ⟨x, sig', heq, -, -, hcltvp, -⟩
  · left
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨hh, hcs⟩
  · cases heq
  · right
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hcltv' : (BitcoinVerify.scriptFlagsOf c.flags).cltv = true := by simp [BitcoinVerify.scriptFlagsOf, hcltv]
    have hclt := (BitcoinHtlc.cltv_concrete (BitcoinVerify.scriptFlagsOf c.flags) (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0
      (BitcoinHtlc.receivedBytes revHash remoteKey localKey payHash expiry) expiry hcltv' (by omega)).1 hcltvp
    obtain ⟨hT, hle, hseq⟩ := (BitcoinHtlc.checkLockTime_iff c.tx c.nIn expiry (by omega) (by simpa [BitcoinBlockV2.LOCKTIME_THRESHOLD] using hexp.2)).1 hclt
    have hl : HeightLocked c.tx := ⟨by omega, by simpa [BitcoinBlockV2.LOCKTIME_THRESHOLD] using hT⟩
    have := (BitcoinHtlcLocks.isFinalTx_height c.tx height blockTime hl c.nIn hnIn
      (by simpa [BitcoinToLocal.inputSequence, BitcoinBlockV2.SEQUENCE_FINAL] using hseq)).1 hfinal
    omega
