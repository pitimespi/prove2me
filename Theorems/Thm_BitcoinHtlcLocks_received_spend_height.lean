import Definitions.Def_BitcoinHtlcLocks
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinHtlc
open BitcoinHtlcLocks BitcoinVerify BitcoinHtlc
open BitcoinScript hiding Bytes Byte

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
      expiry < height := by sorry
