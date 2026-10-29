## The claim

The HTLC mission proved which witnesses spend a received HTLC output under the script interpreter, and that its timeout path runs through `OP_CHECKLOCKTIMEVERIFY <cltv_expiry>`. That is a statement about one script evaluation. The claim Lightning actually needs is one block higher: *no block can contain a non-revocation spend of a received HTLC by the timeout path before the expiry height*. This mission composes the script result with the block mission's finality rule (`IsFinalTx`, required by `ContextualCheckBlock` for every transaction in a block) to state exactly that, and the same bound for a pre-signed HTLC-timeout transaction whose lock time is the expiry.

## What is proved

- **Finality of height-locked transactions** (`isFinalTx_height`): with a nonzero lock time below the threshold and an input that is not `SEQUENCE_FINAL`, a transaction is final at height $h$ iff its lock time is below $h$.
- **Pre-signed HTLC-timeout transactions** (`presigned_timeout_height`): lock time `cltv_expiry` means acceptance only in a block above the expiry.
- **Received HTLC, timeout path** (`received_spend_height`, the goal): a two-element witness accepted by `VerifyScript` for a received HTLC output, in a transaction final at height $h$, is a revocation spend or has `cltv_expiry < h`.

## What this rests on and what it does not say

The composition uses only published theorems: `received_p2wsh_spend`, `cltv_concrete`, `checkLockTime_iff` (HTLC mission) and the block mission's `isFinalTx`. It does not say that a transaction final at a height is in a block at that height, which is the block mission's `ContextualCheckBlock` characterization, nor anything about the offered HTLC's timeout path beyond the pre-signed transaction's own lock time (there the bound rests on the remote node signing only a transaction with that lock time, a key-level fact outside the script). Time-based expiries (lock times at or above the threshold) are excluded by hypothesis; BOLT #3 uses heights. ([BOLT #3](https://github.com/lightning/bolts/blob/master/03-transactions.md#htlc-timeout-and-htlc-success-transactions), [`tx_verify.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp))
