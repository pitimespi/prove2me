## The claim

A Lightning commitment transaction carries one output per in-flight payment: an offered HTLC (the local node pays if the remote reveals the preimage, or recovers the funds after the timeout) or a received HTLC (the local node claims with the preimage before expiry, else the remote takes the funds back). BOLT #3 gives each a witness script with three branches (revocation, preimage, timeout), and the channel's security rests on those three being the only ways to spend. The `to_local` mission proved this for the balance output; this mission proves it for both HTLC scripts, against the script interpreter as transcribed from Bitcoin Core.

## What is proved

- **The opcodes** (`cltv_step`, `multisig_two`): `OP_CHECKLOCKTIMEVERIFY` passes exactly under `CltvPasses`; a 2-of-2 `OP_CHECKMULTISIG` passes iff each signature verifies for its key in order.
- **Each path in closed form** (`offered_revocation`, `offered_preimage`, `offered_timeout`, `received_revocation`, `received_success`, `received_timeout`): on the BOLT #3 witness shapes the interpreter leaves exactly the expected check, including the `NULLDUMMY` condition on the multisig dummy.
- **The spending conditions, for any witness** (`offered_spends_iff`, `received_spends_iff`): over an arbitrary stack, the witness-v0 success condition holds iff one of the three paths' conditions holds. Two facts the interpreter forces that the BOLT text leaves implicit: the inner selector is "is the top element 32 bytes long", not "is it empty"; and every non-revocation path requires the top element not to hash to the revocation hash, because `OP_DUP OP_HASH160 … OP_EQUAL` hashes whatever is on top.
- **The outputs under `VerifyScript`** (`parseScript_offered`, `parseScript_received`, `offered_p2wsh_spend`, `received_p2wsh_spend`, the goal): the byte forms parse as intended, and the pay-to-witness-script-hash outputs are spent exactly by the three paths, with the spending transaction's own signature checker and lock-time check.
- **The lock time** (`cltv_concrete`, `checkLockTime_iff`): with the `CLTV` flag active the check is Core's `CheckLockTime`, which for a block-height expiry is "`nLockTime` is a height at least the expiry and the input is not final".

## What this rests on and what it does not say

The two 20-byte hashes are parameters, not tied to any key or preimage; signature checks stay at the level of the signature mission's checker. The HTLC-success and HTLC-timeout transactions themselves (second-stage, with their own `to_local`-style scripts) and the anchor-output variants of the scripts are not modelled, nor is the protocol-level argument about who holds which key when. ([BOLT #3](https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs), [`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp))
