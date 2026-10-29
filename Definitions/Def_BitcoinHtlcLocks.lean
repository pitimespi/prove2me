import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinBlockV2

/-!
# HTLC lock times at the block level

The HTLC mission proves which witnesses spend a received HTLC output under `VerifyScript`; the
timeout path carries `OP_CHECKLOCKTIMEVERIFY <cltv_expiry>`. The block mission's
`ContextualCheckBlock` requires every transaction of a block to be final (`IsFinalTx`) at the
block's height. This file composes the two: a transaction that spends a received HTLC with a
two-element witness and sits in a block at height `h` is either a revocation spend or has
`cltv_expiry < h`. The same bound holds for a pre-signed HTLC-timeout transaction whose
`nLockTime` is the expiry.
-/

namespace BitcoinHtlcLocks

open BitcoinSer BitcoinScript BitcoinSig BitcoinVerify BitcoinHtlc BitcoinBlockV2

/-- The revocation spend of an HTLC output in context `c`: the witness's public key hashes to the
revocation hash and the signature verifies for it under the context's checker on `script`. -/
def RevocationSpend (c : BitcoinVerify.Ctx) (script revHash pk sig : BitcoinSer.Bytes) : Prop :=
  BitcoinSer.hash160 pk = revHash ∧
    BitcoinSig.checkSigPreTapscript (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 script sig pk = some true

/-- A transaction whose lock time is a block height (nonzero and below the threshold), as a
second-stage HTLC-timeout transaction's is. -/
def HeightLocked (tx : BitcoinSer.Tx) : Prop := 0 < tx.nLockTime ∧ tx.nLockTime < BitcoinBlockV2.LOCKTIME_THRESHOLD

end BitcoinHtlcLocks
