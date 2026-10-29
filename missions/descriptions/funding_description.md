## The claim

A Lightning channel's funds sit in the funding transaction's output, a pay-to-witness-script-hash of the 2-of-2 script `2 <pubkey1> <pubkey2> 2 OP_CHECKMULTISIG`. Everything else in the protocol (commitment transactions, penalties, HTLCs) rests on one fact about this output: it moves only with both parties' signatures. This mission proves that fact against the script interpreter as transcribed from Bitcoin Core, and completes the on-chain script set of a channel begun by the `to_local`, HTLC and anchor missions.

## What is proved

- **The script on its witness** (`funding_witness`): the 2-of-2 loop's verdict, with the `NULLDUMMY` condition on the dummy element.
- **The spending condition, for any witness** (`funding_spends_iff`): the witness-v0 success condition holds iff the stack is exactly `[sig2, sig1, dummy]` with each signature valid for its key in order; no other shape succeeds.
- **The output under `VerifyScript`** (`parseScript_funding`, `funding_p2wsh_spend`, the goal): the byte form parses as intended, and `VerifyScript` accepts a witness for the P2WSH output exactly when it is `dummy sig1 sig2` with both signatures valid for the spending transaction's own checker.

## What this rests on and what it does not say

The signature checks are the signature mission's checker with the witness-v0 sighash; which transaction the signatures commit to (a commitment transaction, a mutual close) is a matter of what was signed, outside the script. BOLT #3's lexicographic ordering of the two keys is not a script-level condition and is not stated. ([BOLT #3](https://github.com/lightning/bolts/blob/master/03-transactions.md#funding-transaction-output), [`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp))
