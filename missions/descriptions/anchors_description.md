## The claim

Modern Lightning channels use `option_anchors`: the remote balance and both HTLC kinds carry a one-block `OP_CHECKSEQUENCEVERIFY` so that a commitment transaction's outputs cannot be spent in the same block it confirms in, and each side gets an *anchor* output that it can spend at any time to bump the fee, and that anyone can sweep after 16 blocks so that anchors do not litter the UTXO set. This mission proves what those scripts enforce, against the script interpreter as transcribed from Bitcoin Core, completing the BOLT #3 commitment-transaction script set begun by the `to_local` and HTLC missions.

## What is proved

- **to_remote** (`to_remote_eval`, `to_remote_spends_iff`, `parseScript_toRemote`, `to_remote_p2wsh_spend`): spendable by the remote key, only after the one-block delay, and by nothing else.
- **Anchor** (`anchor_eval`, `anchor_holder`, `anchor_anyone`, `anchor_spends_iff`, `parseScript_anchor`, `anchor_p2wsh_spend`, `anchor_anyone_concrete`, `anchor_anyone_delay`): the funding-key holder spends at any time; a clean-false signature (the empty signature) spends exactly after the 16-block delay; under the concrete checker, the empty-signature witness verifies iff the spending transaction is version 2 or later with `nSequence ≥ 16`. A signature the checker rejects outright fails the script.
- **HTLCs with anchors** (the six path theorems, the two `spends_iff`, the two parse theorems, the two `p2wsh_spend`): the HTLC mission's three paths each, with the one-block delay added to every non-revocation path and the revocation path unchanged.

## What this rests on and what it does not say

The signature checks stay at the level of the signature mission's checker; the 20-byte hashes are parameters. `anchor_anyone_concrete` holds under consensus flags: under the policy flag `WITNESS_PUBKEYTYPE` an uncompressed funding key would make the empty-signature path fail, which is not modelled. With the `CHECKSEQUENCEVERIFY` flag off (pre-BIP112 blocks) the anchor is spendable by anyone at once; the activation mission fixes the flag on for every current height. The HTLC-success and HTLC-timeout second-stage transactions pay to the `to_local` script, already covered. ([BOLT #3](https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output), [`interpreter.cpp`](https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp))
